
{-
  Author: George Karachalias <george.karachalias@cs.kuleuven.be>
-}

{-# OPTIONS_GHC -Wwarn #-}   -- unused variables

{-# LANGUAGE CPP #-}

module Check ( checkpm, PmResult, pprUncovered, toTcTypeBag ) where

#include "HsVersions.h"

import HsSyn
import TcHsSyn
import DsUtils
import MatchLit
import Id
import ConLike
import DataCon
import Name
import TysWiredIn
import TyCon
import SrcLoc
import Util
import BasicTypes
import Outputable
import FastString

-- For the new checker (We need to remove and reorder things)
import DsMonad ( DsM, initTcDsForSolver, getDictsDs, addDictsDs, getSrcSpanDs)
import TcSimplify( tcCheckSatisfiability )
import UniqSupply (MonadUnique(..))
import TcType ( mkTcEqPred, toTcType, toTcTypeBag )
import Var ( EvVar, varType )
import VarSet
import Type ( substTy, substTys, substTyVars, substTheta, TvSubst
            , expandTypeSynonyms, mkTyConApp
            , tyVarsOfType, tyVarsOfTypes
            , closeOverKinds, varSetElemsKvsFirst )
import TypeRep ( Type(..) )
import Bag
import ErrUtils
import TcMType (genInstSkolTyVars)
import IOEnv (tryM, failM)

import Control.Monad ( forM )
import Control.Applicative (Applicative(..), (<$>))

{-
This module checks pattern matches for:
\begin{enumerate}
  \item Equations that are totally redundant (can be removed from the match)
  \item Exhaustiveness, and returns the equations that are not covered by the match
  \item Equations that are completely overlapped by other equations yet force the
        evaluation of some arguments (but have inaccessible right hand side).
\end{enumerate}

The algorithm used is described in the following paper:
  NO PAPER YET!

%************************************************************************
%*                                                                      *
\subsection{Pattern Match Check Types}
%*                                                                      *
%************************************************************************
-}

-- | Guard representation for the pattern match check. Just represented as a
-- CanItFail for now but can be extended to carry more useful information
type PmGuard = CanItFail

-- | Literal patterns for the pattern match check. Almost identical to LitPat
-- and NPat data constructors of type (Pat id) in file hsSyn/HsPat.lhs
data PmLit id = PmLit HsLit
              | PmOLit (HsOverLit id) (Maybe (SyntaxExpr id)) (SyntaxExpr id)

instance Eq (PmLit id) where
  PmLit  l1            == PmLit  l2            = l1 == l2
  PmOLit l1 Nothing  _ == PmOLit l2 Nothing  _ = l1 == l2
  PmOLit l1 (Just _) _ == PmOLit l2 (Just _) _ = l1 == l2
  _                    == _                    = False

-- | The main pattern type for pattern match check. Only guards, variables,
-- constructors, literals and negative literals. It it sufficient to represent
-- all different patterns, apart maybe from bang and lazy patterns.

-- SPJ... Say that this the term-level stuff only.
-- Drop all types, existential type variables
-- 
data PmPat id = PmGuardPat PmGuard -- Note [Translation to PmPat]
              | PmVarPat { pm_ty :: Type, pm_var :: id }
              | PmConPat { pm_ty :: Type, pm_pat_con :: DataCon, pm_pat_args :: [PmPat id] }
              | PmLitPat { pm_ty :: Type, pm_lit :: PmLit id }
              | PmLitCon { pm_ty :: Type, pm_var :: id, pm_not_lit :: [PmLit id] } -- Note [Negative patterns]

-- | Delta contains all constraints that accompany a pattern vector, including
-- both term-level constraints (guards) and type-lever constraints (EvVars,
-- introduced by GADTs)
data Delta = Delta { delta_evvars :: Bag EvVar -- Type constraints
                   , delta_guards :: PmGuard } -- Term constraints

-- | The result of translation of EquationInfo. The length of the vector may not
-- match the number of the arguments of the match, because guard patterns are
-- interleaved with argument patterns. Note [Translation to PmPat]
type InVec        = [PmPat Id] -- NB: No PmLitCon patterns here
type UncoveredVec = (Delta, [PmPat Id]) -- NB: No guards in the vector, all accumulated in delta

-- | A pattern vector may either force or not the evaluation of an argument.
-- Instead of keeping track of which arguments and under which conditions (like
-- we do in the paper), we simply keep track of if it forces anything or not
-- (That is the only thing that we care about anyway)
type Forces = Bool
type Covers = Bool

-- | The result of pattern match check. A tuple containing:
--   * Clauses that are redundant (do not cover anything, do not force anything)
--   * Clauses with inaccessible rhs (do not cover anything, yet force something)
--   * Uncovered cases (in PmPat form)
type PmResult = ([EquationInfo], [EquationInfo], [UncoveredVec])

type PmM a = DsM a -- just a renaming to remove later (maybe keep this)

{-
%************************************************************************
%*                                                                      *
\subsection{Transform EquationInfos to InVecs}
%*                                                                      *
%************************************************************************

Note [Translation to PmPat]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
The main translation of @Pat Id@ to @PmPat Id@ is performed by @mViewPat@.

Note that it doesn't return a @PmPat Id@ but @[PmPat Id]@ instead. This happens
because some patterns may introduce a guard in the middle of the vector. For example:

\begin{itemize}
  \item View patterns. Pattern @g -> pat@ must be translated to @[x, pat <- g x]@
        where x is a fresh variable
  \item n+k patterns. Pattern @n+k@ must be translated to @[n', n'>=k, let n = n'-k]@
        where @n'@ is a fresh variable
  \item We do something similar with overloaded lists and pattern synonyms since we
        do not know how to handle them yet. They are both translated into a fresh
        variable and a guard that can fail, but doesn't carry any more information
        with it
\end{itemize}

Note [Negative patterns]
~~~~~~~~~~~~~~~~~~~~~~~~
For the repsesentation of literal patterns we use constructors @PmLitPat@ and
@PmLitCon@ (constrained literal pattern). Note that from translating @Pat Id@
we never get a @PmLitCon@. It can appear only in @CoveredVec@ and @UncoveredVec@.
We generate @PmLitCon@s in cases like the following:
\begin{verbatim}
f :: Int -> Int
f 5 = 1
\end{verbatim}

Where we generate an uncovered vector of the form @PmLitCon Int x [5]@ which can
be read as ``all literals @x@ of type @Int@, apart from @5@''.
-}

-- | Transform EquationInfo to a list of PmPats.
preprocess_match :: EquationInfo -> PmM [PmPat Id]
preprocess_match (EqnInfo { eqn_pats = ps, eqn_rhs = mr }) =
  mapM mViewPat ps >>= return . foldr (++) [preprocessMR mr]
  where
    preprocessMR :: MatchResult -> PmPat Id
    preprocessMR (MatchResult can_fail _) = PmGuardPat can_fail

-- | Transform a Pat Id into a list of PmPat Id -- Note [Translation to PmPat]
mViewPat :: Pat Id -> PmM [PmPat Id]
mViewPat pat@(WildPat _) = pure <$> varFromPat pat
mViewPat pat@(VarPat id) = return [PmVarPat (patTypeExpanded pat) id]
mViewPat (ParPat p)      = mViewPat (unLoc p)
mViewPat (LazyPat p)     = mViewPat (unLoc p) -- NOT SURE. IT IS MORE LAZY THAN THAT. USE A FRESH VARIABLE
-- WAS: mViewPat pat@(LazyPat _) = pure <$> varFromPat pat
mViewPat (BangPat p)     = mViewPat (unLoc p)
mViewPat (AsPat _ p)     = mViewPat (unLoc p)
mViewPat (SigPatOut p _) = mViewPat (unLoc p)
mViewPat (CoPat   _ p _) = mViewPat p

-- Unhandled cases. See Note [Translation to PmPat]
mViewPat pat@(NPlusKPat _ _ _ _)                         = unhandled_case pat
mViewPat pat@(ViewPat _ _ _)                             = unhandled_case pat
mViewPat pat@(ListPat _ _ (Just (_,_)))                  = unhandled_case pat
mViewPat pat@(ConPatOut { pat_con = L _ (PatSynCon _) }) = unhandled_case pat

mViewPat pat@(ConPatOut { pat_con = L _ (RealDataCon con), pat_args = ps }) = do
  args <- mViewConArgs con ps
  return [mkPmConPat (patTypeExpanded pat) con args]

mViewPat pat@(NPat lit mb_neg eq) =
  case pmTidyNPat lit mb_neg eq of -- Note [Tidying literals for pattern matching] in MatchLit.lhs
    LitPat lit -> do -- Explain why this is important
      return [PmLitPat (patTypeExpanded pat) (PmLit lit)] -- transformed into simple literal
    NPat lit mb_neg eq ->
      return [PmLitPat (patTypeExpanded pat) (PmOLit lit mb_neg eq)] -- remained as is (not enough information)
    pat -> mViewPat pat -- it was translated to sth else (constructor) -- only with a string this happens

mViewPat pat@(LitPat lit) =
  case pmTidyLitPat lit of -- Note [Tidying literals for pattern matching] in MatchLit.lhs
    LitPat lit -> do
      return [PmLitPat (patTypeExpanded pat) (PmLit lit)]
    pat -> mViewPat pat -- it was translated to sth else (constructor)

mViewPat pat@(ListPat ps _ Nothing) = do
  tidy_ps <- mapM (mViewPat . unLoc) ps
  let mkListPat x y = [mkPmConPat (patTypeExpanded pat) consDataCon (x++y)]
  return $ foldr mkListPat [mkPmConPat (patTypeExpanded pat) nilDataCon []] tidy_ps

-- fake parallel array constructors so that we can handle them
-- like we do with normal constructors
mViewPat pat@(PArrPat ps _) = do
  tidy_ps <- mapM (mViewPat . unLoc) ps
  let fake_con = parrFakeCon (length ps)
  return [mkPmConPat (patTypeExpanded pat) fake_con (concat tidy_ps)]

mViewPat pat@(TuplePat ps boxity _) = do
  tidy_ps <- mapM (mViewPat . unLoc) ps
  let tuple_con = tupleCon (boxityNormalTupleSort boxity) (length ps)
  return [mkPmConPat (patTypeExpanded pat) tuple_con (concat tidy_ps)]

mViewPat (ConPatIn {})      = panic "Check.mViewPat: ConPatIn"
mViewPat (SplicePat {})     = panic "Check.mViewPat: SplicePat"
mViewPat (QuasiQuotePat {}) = panic "Check.mViewPat: QuasiQuotePat"
mViewPat (SigPatIn {})      = panic "Check.mViewPat: SigPatIn"

{-
%************************************************************************
%*                                                                      *
\subsection{Smart Constructors etc.}
%*                                                                      *
%************************************************************************
-}

guardFails :: PmGuard
guardFails = CanFail

guardDoesntFail :: PmGuard
guardDoesntFail = CantFail

guardFailsPat :: PmPat Id
guardFailsPat = PmGuardPat guardFails

freshPmVar :: Type -> PmM (PmPat Id)
freshPmVar ty = do
  unique <- getUniqueM
  let occname = mkVarOccFS (fsLit (show unique))        -- we use the unique as the name (unsafe because
      name    = mkInternalName unique occname noSrcSpan -- we expose it. we need something more elegant
      idname  = mkLocalId name ty
  return (PmVarPat ty idname)

mkPmConPat :: Type -> DataCon -> [PmPat id] -> PmPat id
mkPmConPat ty con pats = PmConPat { pm_ty = ty, pm_pat_con = con, pm_pat_args = pats }

empty_delta :: Delta
empty_delta = Delta emptyBag guardDoesntFail

newEqPmM :: Type -> Type -> PmM EvVar
newEqPmM ty1 ty2 = do
  unique <- getUniqueM
  let name = mkSystemName unique (mkVarOccFS (fsLit "pmcobox"))
  return $ newEvVar name (mkTcEqPred ty1 ty2)

nameType :: String -> Type -> PmM EvVar
nameType name ty = do
  unique <- getUniqueM
  let occname = mkVarOccFS (fsLit (name++"_"++show unique))
  return $ newEvVar (mkInternalName unique occname noSrcSpan) ty

newEvVar :: Name -> Type -> EvVar
newEvVar name ty = mkLocalId name (toTcType ty)

-- (mkConFull K) makes a fresh pattern for K, thus  (K ex1 ex2 d1 d2 x1 x2 x3)
mkConFull :: DataCon -> PmM (PmPat Id, [EvVar])
mkConFull con = do
  subst <- mkConSigSubst con
  let tycon    = dataConOrigTyCon  con                     -- Type constructors
      arg_tys  = substTys    subst (dataConOrigArgTys con) -- Argument types
      univ_tys = substTyVars subst (dataConUnivTyVars con) -- Universal variables (to instantiate tycon)
      ty       = mkTyConApp tycon univ_tys                 -- Type of the pattern
  evvars  <- mapM (nameType "varcon") $ substTheta subst (dataConTheta con) -- Constraints (all of them)
  con_pat <- PmConPat ty con <$> mapM freshPmVar arg_tys
  return (con_pat, evvars)

mkConSigSubst :: DataCon -> PmM TvSubst
-- SPJ: not convinced that we need to make fresh uniques
mkConSigSubst con = do -- INLINE THIS FUNCTION
  loc <- getSrcSpanDs
  (subst, _tvs) <- genInstSkolTyVars loc tkvs
  return subst
  where
    -- Both existential and unviversal type variables
    tyvars = dataConUnivTyVars con ++ dataConExTyVars con
    tkvs   = varSetElemsKvsFirst (closeOverKinds (mkVarSet tyvars))

-- Give up checking the match
give_up :: PmM a
give_up = failM

{-
%************************************************************************
%*                                                                      *
\subsection{Helper functions}
%*                                                                      *
%************************************************************************
-}

-- Approximation
impliesGuard :: Delta -> PmGuard -> Bool
impliesGuard _ CanFail  = False
impliesGuard _ CantFail = True

-- Approximation
forcesGuard :: PmGuard -> Bool
forcesGuard CantFail = False -- it is a True/otherwise
forcesGuard CanFail  = True  -- here we have the approximation

-- Get the type of a pattern with all type synonyms unfolded
patTypeExpanded :: Pat Id -> Type
patTypeExpanded = expandTypeSynonyms . hsPatType

-- Used in all cases that we cannot handle. It generates a fresh variable
-- that has the same type as the given pattern and adds a guard next to it
unhandled_case :: Pat Id -> PmM [PmPat Id]
unhandled_case pat = do
  var_pat <- varFromPat pat
  return [var_pat, guardFailsPat]

-- Generate a variable from the initial pattern
-- that has the same type as the given
varFromPat :: Pat Id -> PmM (PmPat Id)
varFromPat = freshPmVar . patTypeExpanded

mViewConArgs :: DataCon -> HsConPatDetails Id -> PmM [PmPat Id]
mViewConArgs _ (PrefixCon ps)   = concat <$> mapM (mViewPat . unLoc) ps
mViewConArgs _ (InfixCon p1 p2) = concat <$> mapM (mViewPat . unLoc) [p1,p2]
mViewConArgs c (RecCon (HsRecFields fs _))
  | null fs   = instTypesPmM (dataConOrigArgTys c) >>= mapM freshPmVar
  | otherwise = do
      field_pats <- forM (dataConFieldLabels c) $ \lbl -> do
                      let orig_ty = dataConFieldType c lbl
                      ty <- instTypePmM orig_ty -- Expand type synonyms?? Should we? Should we not?
                      -- I am not convinced that we should do this here. Since we recursively call
                      -- mViewPat on the fresh wildcards we have created, we will generate fresh
                      -- variables then. Hence, maybe orig_ty will simply do the job here (I fear
                      -- we instantiate twice without a reason)
                      return (lbl, noLoc (WildPat ty))
                      -- return (lbl, noLoc (WildPat (dataConFieldType c lbl)))
      let all_pats = foldr (\(L _ (HsRecField id p _)) acc -> insertNm (getName (unLoc id)) p acc)
                           field_pats fs
      concat <$> mapM (mViewPat . unLoc . snd) all_pats
  where
    insertNm nm p [] = [(nm,p)]
    insertNm nm p (x@(n,_):xs)
      | nm == n    = (nm,p):xs
      | otherwise  = x : insertNm nm p xs

-- Get all constructors in the family (including given)
allConstructors :: DataCon -> [DataCon]
allConstructors = tyConDataCons . dataConTyCon

-- Fold the arguments back to the constructor:
-- (K p1 .. pn) q1 .. qn         ===> p1 .. pn q1 .. qn     (unfolding)
-- zip_con K (p1 .. pn q1 .. qn) ===> (K p1 .. pn) q1 .. qn (folding)
zip_con :: Type -> DataCon -> [PmPat id] -> [PmPat id]
zip_con ty con pats = (PmConPat ty con con_pats) : rest_pats
  where -- THIS HAS A PROBLEM. WE HAVE TO BE MORE SURE ABOUT THE CONSTRAINTS WE ARE GENERATING
    (con_pats, rest_pats) = splitAtList (dataConOrigArgTys con) pats

-- Add a bag of constraints in delta
addEvVarsDelta :: Bag EvVar -> Delta -> Delta
addEvVarsDelta evvars delta
  = delta { delta_evvars = delta_evvars delta `unionBags` evvars }

-- Add in delta the ev vars from the current local environment
addEnvEvVars :: Delta -> PmM Delta
addEnvEvVars delta = do
  evvars <- getDictsDs
  return (addEvVarsDelta evvars delta)

mapUncovered :: ([PmPat Id] -> [PmPat Id]) -> Bag UncoveredVec -> Bag UncoveredVec
mapUncovered f bag = mapBag (\(delta, vec) -> (delta, f vec)) bag

{-
%************************************************************************
%*                                                                      *
\subsection{Main Pattern Matching Check}
%*                                                                      *
%************************************************************************
-}

-- Forcing part of function `alg'
alg_forces :: UncoveredVec -> InVec -> PmM Forces
alg_forces (_,[])          []                    = return False
alg_forces (delta, _ : us) ((PmVarPat _ _) : ps) = alg_forces (delta, us) ps
alg_forces (delta, (PmConPat _ con1 ps1) : us) ((PmConPat _ con2 ps2) : ps)
  | con1 == con2 = alg_forces (delta, ps1 ++ us) (ps2 ++ ps)
  | otherwise    = return False
alg_forces (_, (PmVarPat _ _):_) ((PmConPat _ _ _) : _) = return True
alg_forces (delta, us) ((PmGuardPat g) : ps) -- return True (too conservative)
  | forcesGuard g = return True -- if it is not a True/otherwise, we consider it forcing sth
  | otherwise     = alg_forces (delta, us) ps
alg_forces (delta, ((PmLitPat _ lit) : us)) ((PmLitPat _ lit') : ps)
  | lit /= lit' = return False
  | otherwise   = alg_forces (delta, us) ps
alg_forces (delta, (PmLitCon _ _ ls) : us) ((PmLitPat _ lit) : ps)
  | lit `elem` ls = return False
  | otherwise     = alg_forces (delta, us) ps
alg_forces (_, (PmVarPat _ _ ) : _) ((PmLitPat _ _) : _) = return True
alg_forces _ _ = give_up

--Covering part of function `alg'
alg_covers :: UncoveredVec -> InVec -> PmM Covers
-- empty
alg_covers (delta,[]) [] = return True -- isSatisfiable delta -- let's leave this aside for now

-- any-var
alg_covers (delta, u : us) ((PmVarPat ty _var) : ps) = do
  evvar <- newEqPmM (pm_ty u) ty
  alg_covers (unitBag evvar `addEvVarsDelta` delta, us) ps

-- con-con
alg_covers (delta, (PmConPat ty1 con1 ps1) : us) ((PmConPat ty2 con2 ps2) : ps)
  | con1 == con2 = alg_covers (delta, ps1 ++ us) (ps2 ++ ps)
  | otherwise    = return False

-- var-con
alg_covers uvec@(delta, (PmVarPat ty _var):us) vec@((PmConPat _ con _) : _) = do
  (con_pat, evvars) <- mkConFull con
  evvar <- newEqPmM ty (pm_ty con_pat)
  alg_covers (listToBag (evvar:evvars) `addEvVarsDelta` delta, con_pat : us) vec

-- any-guard
alg_covers (delta, us) ((PmGuardPat _) : ps) = alg_covers (delta, us) ps

-- lit-lit
alg_covers (delta, (PmLitPat _ lit) : us) ((PmLitPat _ lit') : ps)
  | lit /= lit' = return False
  | otherwise   = alg_covers (delta, us) ps

-- nlit-lit
alg_covers (delta, (PmLitCon _ _ ls) : us) ((PmLitPat _ lit) : ps)
  | lit `elem` ls = return False
  | otherwise     = alg_covers (delta, us) ps

-- var-lit
alg_covers (delta, (PmVarPat _ _ ) : us) ((PmLitPat _ _) : ps) = alg_covers (delta, us) ps

-- give-up
alg_covers _ _ = give_up


-- Compute next uncovered
alg_uncovered :: UncoveredVec -> InVec -> PmM (Bag UncoveredVec)

-- empty
alg_uncovered (_,[]) [] = return emptyBag

-- any-var
alg_uncovered (delta, u : us) ((PmVarPat ty _var) : ps) = do
  evvar  <- newEqPmM (pm_ty u) ty
  triple <- alg_uncovered (unitBag evvar `addEvVarsDelta` delta, us) ps
  return $ mapUncovered (u:) triple

-- con-con
alg_uncovered (delta, uvec@((PmConPat ty1 con1 ps1) : us)) ((PmConPat ty2 con2 ps2) : ps)
  | con1 == con2 = do
      uncovered <- alg_uncovered (delta, ps1 ++ us) (ps2 ++ ps)
      return $ mapUncovered (zip_con ty1 con1) uncovered
  | otherwise = return $ unitBag (delta,uvec)

-- var-con
alg_uncovered uvec@(delta, (PmVarPat ty _var):us) vec@((PmConPat _ con _) : _) = do
  all_con_pats <- mapM mkConFull (allConstructors con)
  uncovered <- forM all_con_pats $ \(con_pat, evvars) -> do
    evvar <- newEqPmM ty (pm_ty con_pat) -- The variable must match with the constructor pattern (alpha ~ T a b c)
    alg_uncovered (listToBag (evvar:evvars) `addEvVarsDelta` delta, con_pat:us) vec
  return $ unionManyBags uncovered

-- any-guard
alg_uncovered (delta, us) ((PmGuardPat guard) : ps) = do
  rec_triple <- alg_uncovered (delta, us) ps
  return $ if delta `impliesGuard` guard
             then rec_triple
             else unitBag (delta,us) `unionBags` rec_triple

-- lit-lit
alg_uncovered (delta, uvec@((p@(PmLitPat _ lit)) : us)) ((PmLitPat _ lit') : ps) -- lit-lit
  | lit /= lit' = return $ unitBag (delta,uvec)
  | otherwise   = mapUncovered (p:) <$> alg_uncovered (delta, us) ps

-- nlit-lit
alg_uncovered (delta, uvec@((PmLitCon ty var ls) : us)) (p@(PmLitPat _ lit) : ps) -- nlit-lit
  | lit `elem` ls = return $ unitBag (delta,uvec)
  | otherwise = do
      rec_triple <- mapUncovered (p:) <$> alg_uncovered (delta, us) ps
      let utriple = unitBag (delta, (PmLitCon ty var (lit:ls)) : us)
      return $ utriple `unionBags` rec_triple

-- var-lit
alg_uncovered (delta, (PmVarPat ty var ) : us) ((p@(PmLitPat _ty2 lit)) : ps) = do
  rec_triple <- mapUncovered (p:) <$> alg_uncovered (delta, us) ps
  let utriple = unitBag (delta, (PmLitCon ty var [lit]) : us)
  return $ utriple `unionBags` rec_triple

-- give-up
alg_uncovered _ _ = give_up


{-
Note [Pattern match check give up]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
There are some cases where we cannot perform the check. A simple example is
trac #322:
\begin{verbatim}
  f :: Maybe Int -> Int
  f 1 = 1
  f Nothing = 2
  f _ = 3
\end{verbatim}

In this case, the first line is compiled as
\begin{verbatim}
  f x | x == fromInteger 1 = 1
\end{verbatim}

To check this match, we should perform arbitrary computations at compile time
(@fromInteger 1@) which is highly undesirable. Hence, we simply give up by
returning a @Nothing@.
-}

process_vector :: Bag UncoveredVec -> InVec -> PmM (Covers, Bag UncoveredVec, Forces) -- Covers , Uncovered, Forces
process_vector uncovered clause = do
  forces     <- anyBagM (\uvec -> alg_forces    uvec clause) uncovered
  covers     <- anyBagM (\uvec -> alg_covers    uvec clause) uncovered
  uncovered' <- mapBagM (\uvec -> alg_uncovered uvec clause) uncovered
  return (covers, concatBag uncovered', forces)

-- | External interface. Takes:
--   * The types of the arguments
--   * The list of EquationInfo to check
-- and returns a (Maybe PmResult) -- see Note [Pattern match check give up]
checkpm :: [Type] -> [EquationInfo] -> DsM (Maybe PmResult)
checkpm tys eq_info = do
  res <- tryM (checkpmPmM tys eq_info)
  case res of
    Left _    -> return Nothing
    Right ans -> return (Just ans)

-- Check the match in PmM monad. Instead of passing the types from the
-- signature to checkpm', we simply use the type information to initialize
-- the first set of uncovered vectors (i.e., a single wildcard-vector).
checkpmPmM :: [Type] -> [EquationInfo] -> PmM PmResult
checkpmPmM _ [] = return ([],[],[])
checkpmPmM tys' eq_infos = do
  let tys = map (toTcType . expandTypeSynonyms) tys' -- Not sure if this is correct
  init_pats  <- mapM freshPmVar tys -- should we expand?
  init_delta <- addEnvEvVars empty_delta
  checkpm' (unitBag (init_delta, init_pats)) eq_infos

-- Worker (recursive)
checkpm' :: Bag UncoveredVec -> [EquationInfo] -> PmM PmResult
checkpm' uncovered_set [] = return ([],[], bagToList uncovered_set)
checkpm' uncovered_set (eq_info:eq_infos) = do
  invec <- preprocess_match eq_info
  (covers, us, forces) <- process_vector uncovered_set invec
  let (redundant, inaccessible)
        | covers    = ([],        [])        -- At least one of cs is satisfiable
        | forces    = ([],        [eq_info]) -- inaccessible rhs
        | otherwise = ([eq_info], [])        -- redundant
  (redundants, inaccessibles, missing) <- checkpm' us eq_infos
  return (redundant ++ redundants, inaccessible ++ inaccessibles, missing)

{-
%************************************************************************
%*                                                                      *
              Interface to the solver
%*                                                                      *
%************************************************************************
-}

-- | This is a hole for a contradiction checker. The actual type must be
-- Delta -> Bool. It should check whether are satisfiable both:
--  * The type constraints
--  * THe term constraints
isSatisfiable :: Delta -> PmM Bool
isSatisfiable (Delta { delta_evvars = evs })
  = do { ((_warns, errs), res) <- initTcDsForSolver $ tcCheckSatisfiability evs
       ; case res of
            Just sat -> return sat
            Nothing  -> pprPanic "isSatisfiable" (vcat $ pprErrMsgBagWithLoc errs) }

{-
%************************************************************************
%*                                                                      *
\subsection{Pretty Printing}
%*                                                                      *
%************************************************************************
-}

instance (OutputableBndr id, Outputable id) => Outputable (PmLit id) where
  ppr (PmLit lit)           = pmPprHsLit lit -- don't use just ppr to avoid all the hashes
  ppr (PmOLit l Nothing  _) = ppr l
  ppr (PmOLit l (Just _) _) = char '-' <> ppr l

instance (OutputableBndr id, Outputable id) => Outputable (PmPat id) where
  ppr (PmGuardPat pm_guard)       = braces $ ptext (sLit "g#")  <> ppr pm_guard -- temporary
  ppr (PmVarPat _ pm_variable)    = ppr pm_variable
  ppr (PmConPat _ pm_con pm_args) | null pm_args = ppr pm_con
                                  | otherwise    = parens $ ppr pm_con <+> hsep (map ppr pm_args)
  ppr (PmLitPat _ pm_literal)     = ppr pm_literal
  ppr (PmLitCon _ var lits)       = ((ppr var) <>) . braces . hcat . punctuate comma . map ppr $ lits

-- Only for debugging
instance Outputable Delta where
  ppr (Delta evvars _) = ppr $ mapBag varType evvars

-- Needs improvement. Now it is too chatty with constraints and does not show
-- PmLitCon s in a nice way
pprUncovered :: UncoveredVec -> SDoc
pprUncovered (delta, uvec) = vcat [ ppr uvec
                                  , nest 4 (ptext (sLit "With constraints:") <+> ppr delta) ]

{-
%************************************************************************
%*                                                                      *
\subsection{Instantiation of types with fresh type & kind variables
%*                                                                      *
%************************************************************************
-}

-- Fresh type with fresh kind
instTypePmM :: Type -> PmM Type
instTypePmM ty = do
  loc <- getSrcSpanDs
  (subst, _tkvs) <- genInstSkolTyVars loc tkvs
  return $ substTy subst ty
  where
    tvs  = tyVarsOfType ty
    tkvs = varSetElemsKvsFirst (closeOverKinds tvs)

instTypesPmM :: [Type] -> PmM [Type]
instTypesPmM tys = do
  loc <- getSrcSpanDs                               -- Location from Monad
  (subst, _tkvs) <- genInstSkolTyVars loc tkvs      -- Generate a substitution for all kind and type variables
  return $ substTys subst tys                       -- Apply it to the original types
  where
    tvs  = tyVarsOfTypes tys                        -- All type variables
    tkvs = varSetElemsKvsFirst (closeOverKinds tvs) -- All tvs and kvs

