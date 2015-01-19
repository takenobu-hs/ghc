
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

-- For the new checker
import DsMonad ( DsM, initTcDsForSolver, getDictsDs, addDictsDs, DsGblEnv, DsLclEnv)
import TcSimplify( tcCheckSatisfiability )
import TcMType (freshTyVarPmM)
import UniqSupply (MonadUnique(..))
import TcType ( TcType, mkTcEqPred, vanillaSkolemTv )
import Var ( EvVar, varType, tyVarKind, tyVarName, mkTcTyVar )
import VarSet
import Type( substTys, substTyVars, substTheta, TvSubst, mkTopTvSubst )
import TypeRep ( Type(..) )
import Bag (Bag, unitBag, listToBag, emptyBag, unionBags, mapBag)
import Type (expandTypeSynonyms, mkTyConApp)
import TcRnTypes (TcRnIf)
import ErrUtils

import Control.Monad ( forM, foldM, liftM2, filterM, replicateM )
import Control.Applicative (Applicative(..), (<$>))

-- Checking Things
import Bag (mapBagM)
import Type (tyVarsOfType)
import Var (setTyVarKind)

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
type InVec = [PmPat Id] -- NB: No PmLitCon patterns here

type CoveredVec   = (Delta, [PmPat Id]) -- NB: No guards in the vector, all accumulated in delta
type UncoveredVec = (Delta, [PmPat Id]) -- NB: No guards in the vector, all accumulated in delta

-- | A pattern vector may either force or not the evaluation of an argument.
-- Instead of keeping track of which arguments and under which conditions (like
-- we do in the paper), we simply keep track of if it forces anything or not
-- (That is the only thing that we care about anyway)
data Forces = Forces | DoesntForce
  deriving (Eq)

-- | Information about a clause.
data PmTriple = PmTriple { pmt_covered   :: [CoveredVec]   -- cases it covers
                         , pmt_uncovered :: [UncoveredVec] -- what remains uncovered
                         , pmt_forces    :: Forces } -- Whether it forces anything

-- | The result of pattern match check. A tuple containing:
--   * Clauses that are redundant (do not cover anything, do not force anything)
--   * Clauses with inaccessible rhs (do not cover anything, yet force something)
--   * Uncovered cases (in PmPat form)
type PmResult = ([EquationInfo], [EquationInfo], [UncoveredVec])

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
mViewPat (LazyPat p)     = mViewPat (unLoc p) -- NOT SURE.
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
    NPat lit mb_neg eq ->
      return [PmLitPat (patTypeExpanded pat) (PmOLit lit mb_neg eq)]
    pat -> mViewPat pat -- it was translated to sth else (simple literal or constructor)

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

freshPmVarNoTy :: PmM (PmPat Id) -- To be used when we have to invent a new type
freshPmVarNoTy = liftPmM freshTyVarPmM >>= freshPmVar

mkWildPat :: PmM (Pat Id)
mkWildPat = liftPmM freshTyVarPmM >>= return . WildPat

mkPmConPat :: Type -> DataCon -> [PmPat id] -> PmPat id
mkPmConPat ty con pats = PmConPat { pm_ty = ty, pm_pat_con = con, pm_pat_args = pats }

empty_triple :: PmTriple
empty_triple = PmTriple [] [] DoesntForce

empty_delta :: Delta
empty_delta = Delta emptyBag guardDoesntFail

newEqPmM :: Type -> Type -> PmM EvVar
newEqPmM ty1 ty2 = do
  unique <- getUniqueM
  let name = mkSystemName unique (mkVarOccFS (fsLit "pmcobox"))
  newEvVar name (mkTcEqPred ty1 ty2)

nameType :: String -> Type -> PmM EvVar
nameType name ty = do
  unique <- getUniqueM
  let occname = mkVarOccFS (fsLit (name++"_"++show unique))
  newEvVar (mkInternalName unique occname noSrcSpan) ty

newEvVar :: Name -> Type -> PmM EvVar
newEvVar name ty
  = do { ty' <- toTcType ty
       ; return (mkLocalId name ty') }

toTcType :: Type -> PmM TcType
toTcType ty = to_tc_type emptyVarSet ty
   where
    to_tc_type :: VarSet -> Type -> PmM TcType
    -- The constraint solver expects EvVars to have TcType, in which the
    -- free type variables are TcTyVars. So we convert from Type to TcType here
    -- A bit tiresome; but one day I expect the two types to be entirely separate
    -- in which case we'll definitely need to do this
    to_tc_type forall_tvs (TyVarTy tv)
      | tv `elemVarSet` forall_tvs = return (TyVarTy tv) -- Sure tv is well-formed ??
      | otherwise = return (TyVarTy (mkTcTyVar (tyVarName tv) (tyVarKind tv) vanillaSkolemTv))
    to_tc_type ftvs (FunTy t1 t2)     = FunTy <$> to_tc_type ftvs t1 <*> to_tc_type ftvs t2
    to_tc_type ftvs (AppTy t1 t2)     = AppTy <$> to_tc_type ftvs t1 <*> to_tc_type ftvs t2
    to_tc_type ftvs (TyConApp tc tys) = TyConApp tc <$> mapM (to_tc_type ftvs) tys
    to_tc_type ftvs (ForAllTy tv ty)  = ForAllTy tv <$> to_tc_type (ftvs `extendVarSet` tv) ty
    to_tc_type ftvs (LitTy l)         = return (LitTy l)

toTcTypeBag :: Bag EvVar -> DsM (Bag EvVar)
toTcTypeBag evvars = do
  (Just ans) <- runPmM $ mapBagM toTc evvars
  return ans
  where
    toTc tyvar = do
      ty' <- toTcType (tyVarKind tyvar)
      return (setTyVarKind tyvar ty')

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
  tvs <- replicateM notys (liftPmM freshTyVarPmM)
  return (mkTopTvSubst (tyvars `zip` tvs))
  where
    -- Both existential and unviversal type variables
    tyvars = dataConUnivTyVars con ++ dataConExTyVars con
    notys  = length tyvars

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
  | null fs   = forM [1..(dataConSourceArity c)] (const freshPmVarNoTy)
  | otherwise = do
      field_pats <- forM (dataConFieldLabels c) $ \x -> do
                      wild_pat <- mkWildPat
                      return (x, noLoc wild_pat)
      let all_pats = foldr (\(L _ (HsRecField id p _)) acc -> insertNm (getName (unLoc id)) p acc)
                           field_pats fs
      concat <$> mapM (mViewPat . unLoc . snd) all_pats
  where
    insertNm nm p [] = [(nm,p)]
    insertNm nm p (x@(n,_):xs)
      | nm == n    = (nm,p):xs
      | otherwise  = x : insertNm nm p xs

forces :: Forces -> Bool
forces Forces      = True
forces DoesntForce = False

or_forces :: Forces -> Forces -> Forces
or_forces f1 f2 | forces f1 || forces f2 = Forces
                | otherwise = DoesntForce

(<+++>) :: PmTriple -> PmTriple -> PmTriple
(<+++>) (PmTriple sc1 su1 sb1) (PmTriple sc2 su2 sb2)
  = PmTriple (sc1++sc2) (su1++su2) (or_forces sb1 sb2)

union_triples :: [PmTriple] -> PmTriple
union_triples = foldr (<+++>) empty_triple

-- Get all constructors in the family (including given)
allConstructors :: DataCon -> [DataCon]
allConstructors = tyConDataCons . dataConTyCon

-- maps only on the vectors
map_triple :: ([PmPat Id] -> [PmPat Id]) -> PmTriple -> PmTriple
map_triple f (PmTriple cs us fs) = PmTriple (mapv cs) (mapv us) fs
  where
    mapv = map $ \(delta, vec) -> (delta, f vec)

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
  evvars <- getDictsPm
  return (addEvVarsDelta evvars delta)

{-
%************************************************************************
%*                                                                      *
\subsection{Substituting Patterns}
%*                                                                      *
%************************************************************************

As described in the paper, during the algorithm we need to substitute term
variables in patterns and guards (in delta). Nevertheless, since we represent
guards as @CanItFail@, there is no reason to substitute in @Delta@.

ToDo: Maybe at least add holes in the implementation using function:
\begin{verbatim}
  substPmGuard :: Id -> PmPat Id -> PmGuard -> PmGuard
  substPmGuard _ _ = id
\end{verbatim}
So that it is more opaque to the internal representation of guards?
-}

-- We substitute only in patterns and not in guards because we do not keep
-- any useful information in guards at this point. In case we extend the
-- syntax of guards, we should also be able to substitute variables in
-- guards as well.
substPmPat :: Id -> PmPat Id -> PmPat Id -> PmPat Id
substPmPat var subst (PmVarPat ty pmvar)
  | var == pmvar = subst -- only case that we actually need to substitute
  | otherwise    = PmVarPat ty pmvar
substPmPat _var _subst (PmGuardPat guard)     = PmGuardPat guard
substPmPat  var  subst (PmConPat ty con args) = PmConPat ty con (map (substPmPat var subst) args)
substPmPat _var _subst p@(PmLitPat _ _)       = p
substPmPat _var _subst p@(PmLitCon _ _ _)     = p -- now that we have a var it may not be correct

substPmVec :: Id -> PmPat Id -> (Delta, [PmPat Id]) -> (Delta, [PmPat Id])
substPmVec var subst (delta, pmvec) = (delta, map (substPmPat var subst) pmvec)

{-
%************************************************************************
%*                                                                      *
\subsection{Main Pattern Matching Check}
%*                                                                      *
%************************************************************************
-}

one_step :: UncoveredVec -> InVec -> PmM PmTriple

-- empty-empty
one_step (delta,[]) [] = do
  delta' <- addEnvEvVars delta
  return $ empty_triple { pmt_covered = [(delta',[])] }

-- any-var
one_step (delta, u : us) ((PmVarPat ty var) : ps) = do
  evvar <- newEqPmM (pm_ty u) ty
  addDictsPm (unitBag evvar) $ do
    triple <- one_step (delta, us) (map (substPmPat var u) ps)
    return $ map_triple (u:) triple

-- con-con
one_step (delta, uvec@((PmConPat ty1 con1 ps1) : us)) ((PmConPat ty2 con2 ps2) : ps)
  | con1 == con2 = do
      evvar <- newEqPmM ty1 ty2 -- Too complex of a constraint you think??
      addDictsPm (unitBag evvar) $ do
        triple <- one_step (delta, ps1 ++ us) (ps2 ++ ps) -- should we do sth about the type constraints here?
        return $ map_triple (zip_con ty1 con1) triple
  | otherwise = do
      delta' <- addEnvEvVars delta
      return $ empty_triple { pmt_uncovered = [(delta',uvec)] }

-- var-con
one_step uvec@(_, (PmVarPat ty var):_) vec@((PmConPat _ con _) : _) = do
  all_con_pats <- mapM mkConFull (allConstructors con)
  triples <- forM all_con_pats $ \(con_pat, evvars) -> do
    evvar <- newEqPmM ty (pm_ty con_pat) -- The variable must match with the constructor pattern (alpha ~ T a b c)
    addDictsPm (listToBag (evvar:evvars)) $
      one_step (substPmVec var con_pat uvec) vec
  let result = union_triples triples
  return $ result { pmt_forces = Forces }

-- any-guard
one_step (delta, us) ((PmGuardPat guard) : ps) = do
  let utriple | delta `impliesGuard` guard = empty_triple
              | otherwise                  = empty_triple { pmt_uncovered = [(delta,us)] }
  rec_triple <- one_step (delta, us) ps
  let result = utriple <+++> rec_triple
  return $ result { pmt_forces = Forces } -- Here we have the conservativity in forcing (a guard always forces sth)

-- lit-lit
one_step (delta, uvec@((p@(PmLitPat _ lit)) : us)) ((PmLitPat _ lit') : ps) -- lit-lit
  | lit /= lit' = do
      delta' <- addEnvEvVars delta
      return $ empty_triple { pmt_uncovered = [(delta',uvec)] }
  | otherwise   = map_triple (p:) <$> one_step (delta, us) ps

-- nlit-lit
one_step (delta, uvec@((PmLitCon ty var ls) : us)) (p@(PmLitPat _ lit) : ps) -- nlit-lit
  | lit `elem` ls = do
      delta' <- addEnvEvVars delta
      return $ empty_triple { pmt_uncovered = [(delta',uvec)] }
  | otherwise = do
      rec_triple <- map_triple (p:) <$> one_step (delta, us) ps
      let utriple = empty_triple { pmt_uncovered = [(delta, (PmLitCon ty var (lit:ls)) : us)] }
      return $ utriple <+++> rec_triple

-- var-lit
one_step (delta, (PmVarPat ty var ) : us) ((p@(PmLitPat ty2 lit)) : ps) = do
  let utriple = empty_triple { pmt_uncovered = [(delta, (PmLitCon ty var [lit]) : us)] }
      subst   = PmLitPat ty2 lit
  rec_triple <- map_triple (p:) <$> one_step (substPmVec var subst (delta, us)) ps
  let result = utriple <+++> rec_triple
  return $ result { pmt_forces = Forces }

one_step _ _ = give_up

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

-- Call one_step on all uncovered vectors and combine the results
one_full_step :: [UncoveredVec] -> InVec -> PmM PmTriple
one_full_step uncovered clause = do
  foldM (\acc uvec -> do
            triple <- one_step uvec clause
            return (triple <+++> acc))
        empty_triple
        uncovered

-- | External interface. Takes:
--   * The types of the arguments
--   * The list of EquationInfo to check
-- and returns a (Maybe PmResult) -- see Note [Pattern match check give up]
checkpm :: [Type] -> [EquationInfo] -> DsM (Maybe PmResult)
checkpm tys = runPmM . checkpmPmM tys

-- Check the match in PmM monad. Instead of passing the types from the
-- signature to checkpm', we simply use the type information to initialize
-- the first set of uncovered vectors (i.e., a single wildcard-vector).
checkpmPmM :: [Type] -> [EquationInfo] -> PmM PmResult
checkpmPmM _ [] = return ([],[],[])
checkpmPmM tys' eq_infos = do
  tys <- mapM toTcType tys' -- Not sure if this is correct
  init_pats  <- mapM (freshPmVar . expandTypeSynonyms) tys -- should we expand?
  init_delta <- addEnvEvVars empty_delta
  checkpm' [(init_delta, init_pats)] eq_infos

-- Worker (recursive)
checkpm' :: [UncoveredVec] -> [EquationInfo] -> PmM PmResult
checkpm' uncovered_set [] = return ([],[],uncovered_set)
checkpm' uncovered_set (eq_info:eq_infos) = do
  invec <- preprocess_match eq_info
  PmTriple cs us fs <- one_full_step uncovered_set invec
  sat_cs <- filterM isSatisfiable cs
  let (redundant, inaccessible)
        | (_:_) <- sat_cs = ([],        [])        -- At least one of cs is satisfiable
        | forces fs       = ([],        [eq_info]) -- inaccessible rhs
        | otherwise       = ([eq_info], [])        -- redundant
  accepted_us <- filterM isSatisfiable us
  (redundants, inaccessibles, missing) <- checkpm' accepted_us eq_infos
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
isSatisfiable :: (Delta, [PmPat Id]) -> PmM Bool
isSatisfiable (Delta { delta_evvars = evs }, _)
  = do { ((warns, errs), res) <- liftPmM $ initTcDsForSolver $
                                 tcCheckSatisfiability evs
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
\subsection{Pattern Matching Monad}
%*                                                                      *
%************************************************************************

The @Pm@ monad. It is just @TcRnIf@ with a possibility of failure
(@Maybe@ monad). Since the only monadic thing we need is fresh term and type
variables, there is no need for it to be in @TcM@ or @DsM@ specifically.
Nevertheless, since we plan to use it in the @DsM@, type synonym @PmM@ is an
instantiation of @Pm@ with the enironments of the desugarer. With small
modifications it could also be used in the @RnM@ or @TcM@.
-}

newtype Pm gbl lcl a = PmM { unPmM :: TcRnIf gbl lcl (Maybe a) }

type PmM a = Pm DsGblEnv DsLclEnv a

runPmM :: PmM a -> DsM (Maybe a)
runPmM = unPmM

instance Functor (Pm gbl lcl) where
  fmap f (PmM m) = PmM $ fmap (fmap f) m

instance Applicative (Pm gbl lcl) where
  pure = PmM . return . return
  (PmM f) <*> (PmM a) = PmM $ liftM2 (<*>) f a

instance Monad (Pm gbl lcl) where
  return = PmM . return . return
  (PmM m) >>= f = PmM $ m >>= \a ->
    case a of Nothing -> return Nothing
              Just x  -> unPmM (f x)

instance MonadUnique (Pm gbl lcl) where
  getUniqueSupplyM = PmM $ getUniqueSupplyM >>= return . return

-- Some more functions lifted from DsM
liftPmM :: DsM a -> PmM a
liftPmM = PmM . fmap Just

getDictsPm :: PmM (Bag EvVar)
getDictsPm = liftPmM getDictsDs

addDictsPm :: Bag EvVar -> PmM a -> PmM a
addDictsPm evvars m = PmM $ do
  result <- addDictsDs evvars (unPmM m)
  return result

-- Give up checking the match
give_up :: PmM a
give_up = PmM $ return Nothing

