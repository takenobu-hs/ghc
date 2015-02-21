
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
import DsMonad ( DsM, initTcDsForSolver, getDictsDs, getSrcSpanDs)
import TcSimplify( tcCheckSatisfiability )
import UniqSupply (MonadUnique(..))
import TcType ( mkTcEqPred, toTcType, toTcTypeBag )
import Var ( EvVar )
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

import Data.Maybe (isJust)
import Control.Monad ( forM, foldM, zipWithM )

import MonadUtils -- MonadIO


import TcRnTypes (pprInTcRnIf)
import Var (varType)

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

-- | Literal patterns for the pattern match check. Almost identical to LitPat
-- and NPat data constructors of type (Pat id) in file hsSyn/HsPat.lhs
data PmLit id = PmLit HsLit
              | PmOLit (HsOverLit id) Bool -- True <=> negated

instance Eq (PmLit id) where
  PmLit  l1       == PmLit  l2       = l1 == l2
  PmOLit l1 True  == PmOLit l2 True  = l1 == l2
  PmOLit l1 False == PmOLit l2 False = l1 == l2
  _               == _               = False

-- | The main pattern type for pattern match check. Only guards, variables,
-- constructors, literals and negative literals. It it sufficient to represent
-- all different patterns, apart maybe from bang and lazy patterns.

-- SPJ... Say that this the term-level stuff only.
-- Drop all types, existential type variables
-- 
data PmPat id = PmGuardPat PmGuard -- Note [Translation to PmPat]
              | PmVarPat Type id
              | PmConPat DataCon [PmPat id]
              | PmLitPat Type (PmLit id)
              | PmLitCon Type [PmLit id] -- Note [Negative patterns]

-- | Guard representation for the pattern match check. Just represented as a
-- CanItFail for now but can be extended to carry more useful information
type PmGuard = CanItFail

-- | A pattern vector may either force or not the evaluation of an argument.
-- Instead of keeping track of which arguments and under which conditions (like
-- we do in the paper), we simply keep track of if it forces anything or not
-- (That is the only thing that we care about anyway)
type Forces = Bool
type Covers = Bool

type SimpleVec = [PmPat Id]        -- NB: No PmGuardPat patterns
type InVec  = [PmPat Id]           -- NB: No PmLitCon patterns
type OutVec = (PmGuard, SimpleVec) -- NB: No PmGuardPat patterns

type Uncovered = Bag OutVec        -- NB: No PmGuardPat patterns
type Covered   = Bag OutVec        -- NB: No PmGuardPat patterns

-- | The result of pattern match check. A tuple containing:
--   * Clauses that are redundant (do not cover anything, do not force anything)
--   * Clauses with inaccessible rhs (do not cover anything, yet force something)
--   * Uncovered cases (in PmPat form)
type PmResult = ([EquationInfo], [EquationInfo], [OutVec])

type PmM a = DsM a -- just a renaming to remove later (maybe keep this)


{-
%************************************************************************
%*                                                                      *
\subsection{Entry point to the checker: checkpm}
%*                                                                      *
%************************************************************************
-}

checkpm :: [Type] -> [EquationInfo] -> DsM (Maybe PmResult)
checkpm tys eq_info
  | null eq_info = return (Just ([],[],[])) -- If we have an empty match, do not reason at all
  | otherwise = do
      loc <- getSrcSpanDs
      pprInTcRnIf (ptext (sLit "Checking match at") <+> ppr loc <+> ptext (sLit "with signature:") <+> ppr tys)
      uncovered0 <- initial_uncovered tys
      let allvanilla = all isVanillaEqn eq_info
      -- Need to pass this to process_vector, so that tc can be avoided
      res <- tryM (checkpm' allvanilla tys uncovered0 eq_info)
      case res of
        Left _    -> return Nothing
        Right ans -> return (Just ans)

-- Worker (recursive)
checkpm' :: Bool -> [Type] -> Uncovered -> [EquationInfo] -> PmM PmResult
checkpm' _vanilla _tys uncovered_set [] = return ([],[], bagToList uncovered_set)
checkpm'  vanilla  tys uncovered_set (eq_info:eq_infos) = do
  invec <- preprocess_match eq_info
  (covers, us, forces) <- process_vector vanilla tys uncovered_set invec
  let (redundant, inaccessible)
        | covers    = ([],        [])        -- At least one of cs is satisfiable
        | forces    = ([],        [eq_info]) -- inaccessible rhs
        | otherwise = ([eq_info], [])        -- redundant
  (redundants, inaccessibles, missing) <- checkpm' vanilla tys us eq_infos
  return (redundant ++ redundants, inaccessible ++ inaccessibles, missing)

-- -----------------------------------------------------------------------
-- | Initial uncovered. This is a set of variables that use the
-- appropriate super kind, the one we get from the signature.
-- Apart from that, the fresh variables have all type variables
-- as type and not something more specific.

initial_uncovered :: [Type] -> PmM Uncovered
initial_uncovered sig = do
  vec <- mapM (freshPmVar . toTcType . expandTypeSynonyms) sig
  return $ unitBag (guardDoesntFail, vec)

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

-- -----------------------------------------------------------------------
-- | Entry point for the translation of source patterns (EquationInfo) to
-- input patterns (InVec).
preprocess_match :: EquationInfo -> PmM [PmPat Id]
preprocess_match (EqnInfo { eqn_pats = ps, eqn_rhs = mr }) =
  mapM mViewPat ps >>= return . foldr (++) [preprocessMR mr]
  where
    preprocessMR :: MatchResult -> PmPat Id
    preprocessMR (MatchResult can_fail _) = PmGuardPat can_fail

-- -----------------------------------------------------------------------
-- | Transform a Pat Id into a list of (PmPat Id) -- Note [Translation to PmPat]
mViewPat :: Pat Id -> PmM [PmPat Id]
mViewPat pat@(WildPat _) = pure <$> varFromPat pat
mViewPat pat@(VarPat id) = return [PmVarPat (patTypeExpanded pat) id]
mViewPat (ParPat p)      = mViewPat (unLoc p)
mViewPat pat@(LazyPat _) = pure <$> varFromPat pat
mViewPat (BangPat p)     = mViewPat (unLoc p)
mViewPat (AsPat _ p)     = mViewPat (unLoc p)
mViewPat (SigPatOut p _) = mViewPat (unLoc p)
mViewPat (CoPat   _ p _) = mViewPat p

-- -----------------------------------------------------------------------
-- | Cases where the algorithm is too conservative. See Note [Translation to PmPat]
mViewPat pat@(NPlusKPat _ _ _ _)                         = unhandled_case pat
mViewPat pat@(ViewPat _ _ _)                             = unhandled_case pat
mViewPat pat@(ListPat _ _ (Just (_,_)))                  = unhandled_case pat
mViewPat pat@(ConPatOut { pat_con = L _ (PatSynCon _) }) = unhandled_case pat

mViewPat (ConPatOut { pat_con = L _ (RealDataCon con), pat_args = ps }) = do
  args <- mViewConArgs con ps
  return [PmConPat con args]

mViewPat pat@(NPat lit mb_neg eq) =
  case pmTidyNPat lit mb_neg eq of -- Note [Tidying literals for pattern matching] in MatchLit.lhs
    LitPat lit -> do -- Explain why this is important
      return [PmLitPat (patTypeExpanded pat) (PmLit lit)] -- transformed into simple literal
    NPat lit mb_neg _eq ->
      return [PmLitPat (patTypeExpanded pat) (PmOLit lit (isJust mb_neg))] -- remained as is (not enough information)
    pat -> mViewPat pat -- it was translated to sth else (constructor) -- only with a string this happens

mViewPat pat@(LitPat lit) =
  case pmTidyLitPat lit of -- Note [Tidying literals for pattern matching] in MatchLit.lhs
    LitPat lit -> do
      return [PmLitPat (patTypeExpanded pat) (PmLit lit)]
    pat -> mViewPat pat -- it was translated to sth else (constructor)

mViewPat (ListPat ps _ Nothing) = do
  tidy_ps <- mapM (mViewPat . unLoc) ps
  let mkListPat x y = [PmConPat consDataCon (x++y)]
  return $ foldr mkListPat [PmConPat nilDataCon []] tidy_ps

-- fake parallel array constructors so that we can handle them
-- like we do with normal constructors
mViewPat (PArrPat ps _) = do
  tidy_ps <- mapM (mViewPat . unLoc) ps
  let fake_con = parrFakeCon (length ps)
  return [PmConPat fake_con (concat tidy_ps)]

mViewPat (TuplePat ps boxity _) = do
  tidy_ps <- mapM (mViewPat . unLoc) ps
  let tuple_con = tupleCon (boxityNormalTupleSort boxity) (length ps)
  return [PmConPat tuple_con (concat tidy_ps)]

mViewPat (ConPatIn {})      = panic "Check.mViewPat: ConPatIn"
mViewPat (SplicePat {})     = panic "Check.mViewPat: SplicePat"
mViewPat (QuasiQuotePat {}) = panic "Check.mViewPat: QuasiQuotePat"
mViewPat (SigPatIn {})      = panic "Check.mViewPat: SigPatIn"

-- -----------------------------------------------------------------------
-- | Trnasform construtor arguments to PmPats. The only reason this is a
-- separate function is that in case of Records, we have to fill the missing
-- arguments with wildcards.
mViewConArgs :: DataCon -> HsConPatDetails Id -> PmM [PmPat Id]
mViewConArgs _ (PrefixCon ps)   = concat <$> mapM (mViewPat . unLoc) ps
mViewConArgs _ (InfixCon p1 p2) = concat <$> mapM (mViewPat . unLoc) [p1,p2]
mViewConArgs c (RecCon (HsRecFields fs _))
  | null fs   = instTypesPmM (dataConOrigArgTys c) >>= mapM freshPmVar
  | otherwise = do
      field_pats <- forM (dataConFieldLabels c) $ \lbl -> do
                      let orig_ty = dataConFieldType c lbl
                      ty <- instTypePmM orig_ty
                      return (lbl, noLoc (WildPat ty))
      let all_pats = foldr (\(L _ (HsRecField id p _)) acc -> insertNm (getName (unLoc id)) p acc)
                           field_pats fs
      concat <$> mapM (mViewPat . unLoc . snd) all_pats
  where
    insertNm nm p [] = [(nm,p)]
    insertNm nm p (x@(n,_):xs)
      | nm == n    = (nm,p):xs
      | otherwise  = x : insertNm nm p xs

{-
%************************************************************************
%*                                                                      *
\subsection{Main Pattern Matching Check}
%*                                                                      *
%************************************************************************
-}

-- -----------------------------------------------------------------------
-- | Not like the paper. This version performs the syntactic part but checks for
-- well-typedness as well. It is like judgement `pm' but returns booleans for
-- redundancy and elimination (not empty/non-empty sets as `pm' does).
process_vector :: Bool -> [Type] -> Uncovered -> InVec -> PmM (Covers, Uncovered, Forces)
process_vector vanilla sig uncovered clause = do
  covered <- alg_covers_many uncovered clause
  covers  <- anyBagM checkwt covered
  forces  <- alg_forces_many uncovered clause
  uncovered    <- alg_uncovered_many uncovered clause
  uncovered_wt <- filterBagM checkwt uncovered
  return (covers, uncovered_wt, forces)
  where
    checkwt = wt sig -- if vanilla -- If all constructors are vanilla constructors, do not bother checking types.
                     --   then \_ -> return True
                     --   else wt sig

-- -----------------------------------------------------------------------
-- | Set versions of `alg_covers', `alg_forces' and `alg_uncovered'
alg_covers_many :: Uncovered -> InVec -> PmM Covered
alg_covers_many uncovered clause = do
  covered <- mapBagM (\uvec -> alg_covers uvec clause) uncovered
  return (concatBag covered)

alg_forces_many :: Uncovered -> InVec -> PmM Bool
alg_forces_many uncovered clause
  = anyBagM (\uvec -> alg_forces uvec clause) uncovered

alg_uncovered_many :: Uncovered -> InVec -> PmM Uncovered
alg_uncovered_many uncovered clause = do
  uncovered' <- mapBagM (\uvec -> alg_uncovered uvec clause) uncovered
  return (concatBag uncovered')


-- COMEHERE: ALL FUNCTIONS BELLOW SHOULD BE CHECKED FOR PROPER TYPING PROPAGATION

-- -----------------------------------------------------------------------
-- | Given an uncovered value vector and a clause, check whether the clause
-- forces the evaluation of any arguments.
alg_forces :: OutVec -> InVec -> PmM Forces

-- empty
alg_forces (_,[]) [] = return False

-- any-var
alg_forces (guards, _ : us) ((PmVarPat _ _) : ps)
  = alg_forces (guards, us) ps

-- con-con
alg_forces (guards, (PmConPat con1 ps1) : us) ((PmConPat con2 ps2) : ps)
  | con1 == con2 = alg_forces (guards, ps1 ++ us) (ps2 ++ ps)
  | otherwise    = return False

-- var-con
alg_forces (_, (PmVarPat _ _):_) ((PmConPat _ _) : _) = return True

-- any-guard
alg_forces (guards, us) ((PmGuardPat g) : ps)
  | forcesGuard g = return True
  | otherwise     = alg_forces (guards, us) ps

-- lit-lit
alg_forces (guards, ((PmLitPat _ lit) : us)) ((PmLitPat _ lit') : ps)
  | lit /= lit' = return False
  | otherwise   = alg_forces (guards, us) ps

-- nlit-lit
alg_forces (guards, (PmLitCon _ ls) : us) ((PmLitPat _ lit) : ps)
  | lit `elem` ls = return False
  | otherwise     = alg_forces (guards, us) ps

-- var-lit
alg_forces (_, (PmVarPat _ _ ) : _) ((PmLitPat _ _) : _) = return True

-- give-up
alg_forces _ _ = give_up

-- -----------------------------------------------------------------------
-- | Given an uncovered value vector and a clause, compute the subset of vectors
-- that remain uncovered.
alg_uncovered :: OutVec -> InVec -> PmM Uncovered

-- empty
alg_uncovered (_,[]) [] = return emptyBag

-- any-var
alg_uncovered (guards, u : us) ((PmVarPat _ty _var) : ps) =
  mapOutVecBag (u:) <$> alg_uncovered (guards, us) ps

-- con-con
alg_uncovered (guards, uvec@((PmConPat con1 ps1) : us)) ((PmConPat con2 ps2) : ps)
  | con1 == con2 = mapOutVecBag (zip_con con1) <$> alg_uncovered (guards, ps1 ++ us) (ps2 ++ ps)
  | otherwise    = return $ unitBag (guards, uvec)

-- var-con
alg_uncovered (guards, (PmVarPat _ty _var):us) vec@((PmConPat con _) : _) = do
  all_con_pats <- mapM mkConFull (allConstructors con)
  uncovered <- forM all_con_pats $ \con_pat ->
    alg_uncovered (guards, con_pat:us) vec
  return $ unionManyBags uncovered

-- any-guard
alg_uncovered (guards, us) ((PmGuardPat g) : ps) = do
  rec_uncovered <- alg_uncovered (guards, us) ps
  return $ if guards `impliesGuard` g
             then rec_uncovered
             else (guards,us) `consBag` rec_uncovered

-- lit-lit
alg_uncovered (guards, uvec@((p@(PmLitPat _ lit)) : us)) ((PmLitPat _ lit') : ps)
  | lit /= lit' = return $ unitBag (guards, uvec)
  | otherwise   = mapOutVecBag (p:) <$> alg_uncovered (guards, us) ps

-- nlit-lit
alg_uncovered (guards, uvec@((PmLitCon ty ls) : us)) (p@(PmLitPat _ lit) : ps)
  | lit `elem` ls = return $ unitBag (guards, uvec)
  | otherwise = do
      rec_uncovered <- mapOutVecBag (p:) <$> alg_uncovered (guards, us) ps
      let u_uncovered = (guards, (PmLitCon ty (lit:ls)) : us)
      return $ u_uncovered `consBag` rec_uncovered

-- var-lit
alg_uncovered (guards, (PmVarPat ty _var) : us) ((p@(PmLitPat _ty2 lit)) : ps) = do
  rec_uncovered <- mapOutVecBag (p:) <$> alg_uncovered (guards, us) ps
  let u_uncovered = (guards, (PmLitCon ty [lit]) : us)
  return $ u_uncovered `consBag` rec_uncovered

-- give-up
alg_uncovered _ _ = give_up

-- -----------------------------------------------------------------------
-- | Given an uncovered value vector and a clause, compute the covered set of
-- the clause. We represent it as a set but it is always empty or a singleton.
alg_covers :: OutVec -> InVec -> PmM Covered

-- empty
alg_covers (guards,[]) [] = return $ unitBag (guards, [])

-- any-var
alg_covers (guards, u : us) ((PmVarPat _ty _var) : ps)
  = mapOutVecBag (u:) <$> alg_covers (guards, us) ps

-- con-con
alg_covers (guards, (PmConPat con1 ps1) : us) ((PmConPat con2 ps2) : ps)
  | con1 == con2 = mapOutVecBag (zip_con con1) <$> alg_covers (guards, ps1 ++ us) (ps2 ++ ps)
  | otherwise    = return emptyBag

-- var-con
alg_covers (guards, (PmVarPat _ty _var):us) vec@((PmConPat con _) : _) = do
  con_pat <- mkConFull con
  alg_covers (guards, con_pat : us) vec

-- any-guard
alg_covers (guards, us) ((PmGuardPat _) : ps) = alg_covers (guards, us) ps -- actually this is an `and` operation be we never check guard on cov

-- lit-lit
alg_covers (guards, u@(PmLitPat _ lit) : us) ((PmLitPat _ lit') : ps)
  | lit /= lit' = return emptyBag
  | otherwise   = mapOutVecBag (u:) <$> alg_covers (guards, us) ps

-- nlit-lit
alg_covers (guards, u@(PmLitCon _ ls) : us) ((PmLitPat _ lit) : ps)
  | lit `elem` ls = return emptyBag
  | otherwise     = mapOutVecBag (u:) <$> alg_covers (guards, us) ps

-- var-lit
alg_covers (guards, (PmVarPat _ _ ) : us) (p@(PmLitPat _ _) : ps)
  = mapOutVecBag (p:) <$> alg_covers (guards, us) ps

-- give-up
alg_covers _ _ = give_up

{-
%************************************************************************
%*                                                                      *
\subsection{Instantiation of types with fresh type & kind variables}
%*                                                                      *
%************************************************************************
-}

-- -----------------------------------------------------------------------
-- | Given a type, instantiate all its type and kind variables with fresh.
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
  loc <- getSrcSpanDs
  (subst, _tkvs) <- genInstSkolTyVars loc tkvs
  return $ substTys subst tys
  where
    tvs  = tyVarsOfTypes tys
    tkvs = varSetElemsKvsFirst (closeOverKinds tvs)

{-
%************************************************************************
%*                                                                      *
\subsection{Typing phase}
%*                                                                      *
%************************************************************************
-}

-- -----------------------------------------------------------------------
-- | Check whether all constructor patterns that appear in the match are
-- boring haskell98 constructors (No existentials etc.). If that's the case,
-- process_vector does not have to type check the clauses (yet, it generates
-- the constraints - we may have to change this for efficiency).
isVanillaEqn :: EquationInfo -> Bool
isVanillaEqn (EqnInfo { eqn_pats = pats }) = all isVanillaPat pats

-- -----------------------------------------------------------------------
-- | Interface to the solver
-- This is a hole for a contradiction checker. The actual type must be
-- (Bag EvVar, PmGuard) -> Bool. It should check whether are satisfiable both:
--  * The type constraints
--  * THe term constraints
isSatisfiable :: Bag EvVar -> PmM Bool
isSatisfiable evs
  = do { ((_warns, errs), res) <- initTcDsForSolver $ tcCheckSatisfiability evs
       ; case res of
            Just sat -> return sat
            Nothing  -> pprPanic "isSatisfiable" (vcat $ pprErrMsgBagWithLoc errs) }

-- -----------------------------------------------------------------------
-- | Infer types
-- INVARIANTS:
-- 1) ALL PmLit and PmLitCon have the EXACT type (inherit it carefully while checking uncovered).
-- 2) ALL PmVarPat have fresh type, with the correct super kind
inferTyPmPat :: PmPat Id -> PmM (Type, Bag EvVar) -- infer a type and a set of constraints
inferTyPmPat (PmGuardPat  _) = panic "inferTyPmPat: PmGuardPat"
inferTyPmPat (PmVarPat ty _) = return (ty, emptyBag) -- instTypePmM ty >>= \ty' -> return (ty', emptyBag)
inferTyPmPat (PmLitPat ty _) = return (ty, emptyBag)
inferTyPmPat (PmLitCon ty _) = return (ty, emptyBag)
inferTyPmPat (PmConPat con args) = do
  (tys, cs) <- inferTyPmPats args -- Infer argument types and respective constraints (Just like the paper)
  subst  <- mkConSigSubst con      -- Create the substitution theta (Just like the paper)
  let tycon    = dataConTyCon con -- JUST A TEST dataConOrigTyCon  con                     -- Type constructor
      arg_tys  = substTys    subst (dataConOrigArgTys con) -- Argument types
      univ_tys = substTyVars subst (dataConUnivTyVars con) -- Universal variables (to instantiate tycon)
      tau      = mkTyConApp tycon univ_tys                 -- Type of the pattern

  pprInTcRnIf (ptext (sLit "pattern:") <+> ppr (PmConPat con args) <+> ptext (sLit "has univ tys length:") <+> ppr (length univ_tys))
  con_thetas <- mapM (nameType "varcon") $ substTheta subst (dataConTheta con) -- Constraints from the constructor signature
  eq_thetas  <- foldM (\acc (ty1, ty2) -> do
                          eq_theta <- newEqPmM ty1 ty2
                          return (eq_theta `consBag` acc))
                      cs (tys `zip` arg_tys)
  return (tau, listToBag con_thetas `unionBags` eq_thetas)

inferTyPmPats :: [PmPat Id] -> PmM ([Type], Bag EvVar)
inferTyPmPats pats = do
  tys_cs <- mapM inferTyPmPat pats
  let (tys, cs) = unzip tys_cs
  return (tys, unionManyBags cs)

-- -----------------------------------------------------------------------
-- | Given a signature sig and an output vector, check whether the vector's type
-- can match the signature
wt :: [Type] -> OutVec -> PmM Bool
wt sig (_, vec)
  | length sig == length vec = do
      (tys, cs) <- inferTyPmPats vec
      cs' <- zipWithM newEqPmM (map expandTypeSynonyms sig) tys -- The vector should match the signature type
      env_cs <- getDictsDs
      loc <- getSrcSpanDs
      pprInTcRnIf (ptext (sLit "Checking in location:") <+> ppr loc)
      pprInTcRnIf (ptext (sLit "Checking vector") <+> ppr vec <+> ptext (sLit "with inferred type:") <+> ppr tys)
      pprInTcRnIf (ptext (sLit "With given signature:") <+> ppr sig)
      let constraints = listToBag cs' `unionBags` cs `unionBags` env_cs
      pprInTcRnIf (ptext (sLit "Constraints:") <+> ppr (mapBag varType constraints))
      isSatisfiable constraints
  | otherwise = pprPanic "wt: length mismatch:" (ppr sig $$ ppr vec)

{-
%************************************************************************
%*                                                                      *
\subsection{Misc. (Smart constructors, helper functions, etc.)}
%*                                                                      *
%************************************************************************
-}

-- -----------------------------------------------------------------------
-- | Guards

guardFails :: PmGuard
guardFails = CanFail

guardDoesntFail :: PmGuard
guardDoesntFail = CantFail

impliesGuard :: PmGuard -> PmGuard -> Bool
impliesGuard _ CanFail  = False -- conservative
impliesGuard _ CantFail = True

forcesGuard :: PmGuard -> Bool
forcesGuard CantFail = False
forcesGuard CanFail  = True -- conservative

-- -----------------------------------------------------------------------
-- | Translation of source patterns to PmPat Id

guardFailsPat :: PmPat Id
guardFailsPat = PmGuardPat guardFails

freshPmVar :: Type -> PmM (PmPat Id)
freshPmVar ty = do
  unique <- getUniqueM
  let occname = mkVarOccFS (fsLit (show unique))        -- we use the unique as the name (unsafe because
      name    = mkInternalName unique occname noSrcSpan -- we expose it. we need something more elegant
      idname  = mkLocalId name ty
  return (PmVarPat ty idname)

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

-- -----------------------------------------------------------------------
-- | Types and constraints

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

-- Get the type of a pattern with all type synonyms unfolded
patTypeExpanded :: Pat Id -> Type
patTypeExpanded = expandTypeSynonyms . hsPatType

-- -----------------------------------------------------------------------
-- | Other utility functions for main check

-- (mkConFull K) makes a fresh pattern for K, thus  (K ex1 ex2 d1 d2 x1 x2 x3)
mkConFull :: DataCon -> PmM (PmPat Id)
mkConFull con = do
  subst <- mkConSigSubst con
  let arg_tys = substTys subst (dataConOrigArgTys con) -- Argument types
  PmConPat con <$> mapM freshPmVar arg_tys

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

-- Get all constructors in the family (including given)
allConstructors :: DataCon -> [DataCon]
allConstructors = tyConDataCons . dataConTyCon

-- Fold the arguments back to the constructor:
-- (K p1 .. pn) q1 .. qn         ===> p1 .. pn q1 .. qn     (unfolding)
-- zip_con K (p1 .. pn q1 .. qn) ===> (K p1 .. pn) q1 .. qn (folding)
zip_con :: DataCon -> [PmPat id] -> [PmPat id]
zip_con con pats = (PmConPat con con_pats) : rest_pats
  where -- THIS HAS A PROBLEM. WE HAVE TO BE MORE SURE ABOUT THE CONSTRAINTS WE ARE GENERATING
    (con_pats, rest_pats) = splitAtList (dataConOrigArgTys con) pats

mapOutVecBag :: ([PmPat Id] -> [PmPat Id]) -> Bag OutVec -> Bag OutVec
mapOutVecBag f bag = mapBag (\(guards, vec) -> (guards, f vec)) bag

-- See Note [Pattern match check give up]
give_up :: PmM a
give_up = failM

{-
%************************************************************************
%*                                                                      *
\subsection{Pretty Printing}
%*                                                                      *
%************************************************************************
-}

pprUncovered :: OutVec -> SDoc
pprUncovered = pprOutVec

-- Needed only for missing. Inaccessibles and redundants are handled already.
pprOutVec :: OutVec -> SDoc
pprOutVec (_, []  ) = panic "pprOutVec: empty vector"
pprOutVec (_, [p] ) = ppr p
pprOutVec (_, pats) = pprWithParens pats

pprWithParens :: (OutputableBndr id) => [PmPat id] -> SDoc
pprWithParens pats = sep (map paren_if_needed pats)
  where paren_if_needed p
          | PmConPat _ args <- p
          , not (null args) = parens (ppr p)
          | otherwise       = ppr p

-- | Pretty print list [1,2,3] as the set {1,2,3}
-- {COMEHERE: FRESH VARIABLE and "where .. not one of ..."}
pprSet :: Outputable id => [id] -> SDoc
pprSet lits = braces $ sep $ punctuate comma $ map ppr lits

instance (OutputableBndr id) => Outputable (PmLit id) where
  ppr (PmLit lit)      = pmPprHsLit lit -- don't use just ppr to avoid all the hashes
  ppr (PmOLit l False) = ppr l
  ppr (PmOLit l True ) = char '-' <> ppr l

-- We do not need the (OutputableBndr id, Outputable id) because we print all
-- variables as wildcards at the end so we do not really care about them.
instance (OutputableBndr id) => Outputable (PmPat id) where
  ppr (PmGuardPat _)      = panic "ppr: PmPat id: PmGuardPat"
  ppr (PmVarPat _ _)      = underscore
  ppr (PmConPat con args) = sep [ppr con, pprWithParens args]
  ppr (PmLitPat _ lit)    = ppr lit
  ppr (PmLitCon _ lits)   = pprSet lits

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

