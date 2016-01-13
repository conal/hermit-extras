{-# LANGUAGE CPP, Rank2Types, ConstraintKinds, PatternGuards, ViewPatterns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables, TupleSections, LambdaCase #-}
{-# LANGUAGE DeriveDataTypeable, DeriveFunctor, DeriveFoldable, TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-} -- see below
-- {-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  HERMIT.Extras
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Some definitions useful with HERMIT.
----------------------------------------------------------------------

-- #define WatchFailures

module HERMIT.Extras
  ( -- * Misc
    Unop, Binop
    -- * Core utilities
  , unsafeShowPpr
  , isType, exprType',exprTypeT, pairTy
  , tcFind0, tcFind, tcFind2
  , tcApp0, tcApp1, tcApp2
  , isPairTC, isPairTy, isEitherTy
  , isUnitTy, isBoolTy, isIntTy
  , onCaseAlts, onAltRhs, unliftedType
  , apps, apps', apps1', callSplitT, callNameSplitT, unCall, unCall1
  , collectForalls, subst, isTyLam, setNominalRole_maybe
  , isVarT, isLitT, isWorker, isWorkerT
  , repr
{-
  , varOccCount, oneOccT, castOccsSame
-}
  , exprAsConApp
    -- * HERMIT utilities
  , moduledName
  , newIdT
  , liftedKind, unliftedKind
  , ReType, ReExpr, ReBind, ReAlt, ReProg, ReCore, ReLCore
  , FilterH, FilterE, FilterTy, OkCM, TransformU
  , findTyConT, tyConApp1T
  , isTypeE, isCastE, isDictE, isCoercionE
  , mkUnit, mkPair, mkLeft, mkRight, mkEither
  , InCoreTC
  , Observing, observeR', tries, triesL, scopeR, labeled
  , lintExprR -- , lintExprDieR
  , lintingExprR
  , varLitE, uqVarName, fqVarName, typeEtaLong, simplifyE
  , walkE , alltdE, anytdE, anybuE, onetdE, onebuE
  , inAppTys, isAppTy, inlineWorkerR
  , letFloatToProg
  , concatProgs
  , rejectR , rejectTypeR
  , simplifyExprR, changedSynR, changedArrR
  , showPprT, stashLabel, tweakLabel
{-
  , saveDefT, findDefT
  , saveDefNoFloatT, dumpStashR, dropStashedLetR
-}
  , unJustT, tcViewT, unFunCo
  , lamFloatCastR{-, castFloatLamR-}, castCastR, unCastCastR, castTransitiveUnivR
  , castFloatAppR',castFloatAppUnivR, castFloatCaseR, castFloatApps
  , caseFloatR', caseWildR
  , bashExtendedWithE, bashUsingE, bashE
--   , bashExtendedWithE', bashR', bashE'
  , buildDictionaryT', buildTypeableT', simpleDict
  , TransformM, RewriteM
  , repeatN
  , progRhsAnyR
  , ($*), pairT, listT, unPairR
  , externC, externC'
  , normaliseTypeT, normalizeTypeT, optimizeCoercionR, optimizeCastR
  , bindUnLetIntroR
  -- , letFloatCaseAltR
  , trivialExpr, letSubstTrivialR, betaReduceTrivialR
  -- , pruneAltsExpr, pruneAltsR -- might remove
  , extendTvSubstVars
  , retypeExprR
  , Tree(..), toTree, foldMapT, foldT
  , SyntaxEq(..)
  , regularizeType
  , cseGuts, cseProg, cseBind, cseExpr
  , letNonRecSubstSafeR', simplifyR'
  ) where

import Prelude hiding (id,(.),foldr)

import Data.Monoid (Monoid(..),(<>),Sum(..))
import Control.Category (Category(..),(>>>))
import Data.Functor ((<$>),(<$))
import Data.Foldable (Foldable(..))
import Control.Applicative (Applicative(..),liftA2,(<|>))
import Control.Monad ((<=<),unless,when)
import Control.Arrow (Arrow(..),(>>^))
import Data.Maybe (catMaybes,fromMaybe)
import Data.List (intercalate,isPrefixOf)
import Text.Printf (printf)
import Data.Typeable (Typeable)
import Control.Monad.IO.Class (MonadIO)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Char (isUpper,isSpace)
import Data.String (fromString)

-- GHC
import Unique(hasKey)
import PrelNames (
  liftedTypeKindTyConKey,unliftedTypeKindTyConKey,constraintKindTyConKey,
  eitherTyConName)
import SimplCore (simplifyExpr)
import FamInstEnv (normaliseType)
import qualified Coercion
import OptCoercion (optCoercion)
import Type (substTy,substTyWith)
import TcType (isUnitTy,isBoolTy,isIntTy)
import Unify (tcUnifyTy)
-- import TyCoRep ()
import CSE (cseProgram)

-- import Language.KURE.Transform (apply)
import HERMIT.Core
  ( CoreProg(..),Crumb,bindsToProg,progToBinds,freeVarsExpr
  , progSyntaxEq,bindSyntaxEq,defSyntaxEq,exprSyntaxEq
  , altSyntaxEq,typeSyntaxEq,coercionSyntaxEq
  , CoreDef(..),defToIdExpr, coercionAlphaEq,localFreeVarsExpr)
import HERMIT.Name (newIdH,mkQualified)
import HERMIT.Monad
  (HermitM,HasHermitMEnv,getModGuts,LiftCoreM,getHscEnv)
import HERMIT.Context
  ( BoundVars(..),AddBindings(..),ReadBindings(..)
  , HasEmptyContext(..), HasCoreRules(..)
  , HermitC, LemmaContext )
-- Note that HERMIT.Dictionary re-exports HERMIT.Dictionary.*
import HERMIT.Dictionary
  ( findIdT, findTyConT, callT, callNameT, simplifyR, letFloatTopR, letSubstR, betaReduceR
  , observeR, bracketR, bashExtendedWithR, bashUsingR, bashR, bashComponents
  , wrongExprForm
  , castFloatAppR, castFloatLamR
  , caseFloatCastR, caseFloatCaseR, caseFloatAppR, caseFloatLetR
  , unshadowR, lintExprT{-, inScope-}, inlineR, buildDictionaryT
  , unfoldPredR
  , buildTypeable
  , traceR
  -- Remembered
  , rememberR, unfoldRememberedR
  -- For simplify' and letNonRecSubstSafeR'
  , letNonRecSubstR, arityOf,varBindingDepthT,exprIsOccurrenceOfT
  , recToNonrecR, unfoldBasicCombinatorR, betaReducePlusR
  , caseReduceR, letElimR
  )
-- import HERMIT.Dictionary (traceR)
import HERMIT.GHC hiding (FastString(..),(<>),substTy)
import HERMIT.Kure hiding (apply,(<$>),(<*>))
import HERMIT.External (External,Extern(..),external,ExternalName)
import HERMIT.Name (HermitName)
import HERMIT.Lemma (Used(..))

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

-- | Unary transformation
type Unop a = a -> a

-- | Binary transformation
type Binop a = a -> Unop a

{--------------------------------------------------------------------
    Core utilities
--------------------------------------------------------------------}

-- | 'showPpr' with global dynamic flags
unsafeShowPpr :: Outputable a => a -> String
unsafeShowPpr = showPpr unsafeGlobalDynFlags

onCaseAlts :: (ExtendCrumb c, ReadCrumb c, AddBindings c, Monad m) =>
              Rewrite c m CoreAlt -> Rewrite c m CoreExpr
onCaseAlts r = caseAllR id id id (const r)

-- | Rewrite a case alternative right-hand side.
onAltRhs :: (Functor m, Monad m) =>
            Rewrite c m CoreExpr -> Rewrite c m CoreAlt
onAltRhs r = do (con,vs,rhs) <- id
                (con,vs,) <$> r $* rhs

-- Form an application to type and value arguments.
apps :: Id -> [Type] -> [CoreExpr] -> CoreExpr
apps f ts es
  | tyArity f /= length ts =
      error $ printf "apps: Id %s wants %d type arguments but got %d."
                     (fqVarName f) arity ntys
  | otherwise = mkApps (varToCoreExpr f) (map Type ts ++ es)
 where
   arity = tyArity f
   ntys  = length ts

-- Note: With unlifted types, mkCoreApps might make a case expression.
-- If we don't want to, maybe use mkApps.

-- Number of type arguments.
tyArity :: Id -> Int
tyArity = length . fst . splitForAllTys . varType

-- exprType gives an obscure warning when given a Type expression.
exprType' :: CoreExpr -> Type
exprType' (Type {}) = error "exprType': given a Type"
exprType' e         = exprType e

-- Like 'exprType', but fails if given a type.
exprTypeT :: Monad m => Transform c m CoreExpr Type
exprTypeT =
  do e <- idR
     guardMsg (not (isType e)) "exprTypeT: given a Type"
     return (exprType' e)

-- TODO: redefine exprTypeT via HERMIT's more exprTypeM

isType :: CoreExpr -> Bool
isType (Type {}) = True
isType _         = False

pairTy :: Binop Type
pairTy a b = mkBoxedTupleTy [a,b]

tcApp0 :: TyCon -> Type
tcApp0 tc = TyConApp tc []

tcApp1 :: TyCon -> Unop Type
tcApp1 tc a = TyConApp tc [a]

tcApp2 :: TyCon -> Binop Type
tcApp2 tc a b = TyConApp tc [a,b]

isPairTC :: TyCon -> Bool
isPairTC tc = isBoxedTupleTyCon tc && tupleTyConArity tc == 2

isPairTy :: Type -> Bool
isPairTy (TyConApp tc [_,_]) = isBoxedTupleTyCon tc
isPairTy _                   = False

isEitherTy :: Type -> Bool
isEitherTy (TyConApp tc [_,_]) = tyConName tc == eitherTyConName
isEitherTy _                   = False

liftedKind :: Kind -> Bool
liftedKind (TyConApp tc []) =
  any (tc `hasKey`) [liftedTypeKindTyConKey, constraintKindTyConKey]
liftedKind _                = False

unliftedKind :: Kind -> Bool
unliftedKind (TyConApp tc []) = tc `hasKey` unliftedTypeKindTyConKey
unliftedKind _                = False

-- TODO: Switch to isLiftedTypeKind and isUnliftedTypeKind from Kind (in GHC).
-- When I tried earlier, I lost my inlinings. Investigate!
-- <https://github.com/conal/type-encode/issues/1>

unliftedType :: Type -> Bool
unliftedType = unliftedKind . typeKind

splitTysVals :: [Expr b] -> ([Type], [Expr b])
splitTysVals (Type ty : rest) = first (ty :) (splitTysVals rest)
splitTysVals rest             = ([],rest)

collectForalls :: Type -> ([Var], Type)
collectForalls ty = go [] ty
  where
    go vs (ForAllTy v t') = go (v:vs) t'
    go vs t               = (reverse vs, t)

-- TODO: Rewrite collectTypeArgs and collectForalls as unfolds and refactor.

-- | Substitute new subexpressions for variables in an expression
subst :: [(Id,CoreExpr)] -> Unop CoreExpr
subst ps = substExpr (error "subst: no SDoc") (foldr add emptySubst ps)
 where
   add (v,new) sub = extendIdSubst sub v new

isTyLam :: CoreExpr -> Bool
isTyLam (Lam v _) = isTyVar v
isTyLam _         = False

type ExtendCrumb c = ExtendPath c Crumb
type ReadCrumb   c = ReadPath   c Crumb

isVarT :: (Monad m, ExtendCrumb c) =>
          Transform c m CoreExpr ()
isVarT = varT successT

isLitT :: (Monad m, ExtendCrumb c) =>
          Transform c m CoreExpr ()
isLitT = litT successT

-- | Abbreviation for the 'Representational' role
repr :: Role
repr = Representational

#if __GLASGOW_HASKELL__ < 709

-- | Number of occurrences of a non-type variable
varOccCount :: Var -> CoreExpr -> Int
varOccCount v = occs
 where
   occs :: CoreExpr -> Int
   occs (Var u) | u == v    = 1
                | otherwise = 0
   occs (Lit _)             = 0
   occs (App p q)           = occs p + occs q
   occs (Lam _ e)           = occs e  -- assumes no shadowning
   occs (Let b e)           = bindOccs b + occs e
   occs (Case e _ _ alts)   = occs e + sum (map altOccs alts)
   occs (Cast e _)          = occs e
   occs (Tick _ e)          = occs e
   occs (Type _)            = 0
   occs (Coercion _)        = 0
   altOccs (_,_,e)          = occs e
   bindOccs (NonRec _ e)    = occs e
   bindOccs (Rec bs)        = sum (map (occs . snd) bs)

-- TODO: stricter version

#if 0
-- | Number of occurrences of a non-type variable
varOccCount :: Var -> CoreExpr -> Int
varOccCount v = occs 0
 where
   occs !n (Var u) | u == v = n+1
   occs !n (App p q)        = occs (occs n p) q
   occs !n (Lam _ e)        = occs n e  -- assumes no shadowning
   occs !n (Cast e _)       = occs n e
   occs !n (Tick _ e)       = occs n e
   occs !n _                = n
#endif

-- | Matches a let binding with exactly one occurrence of the variable.
oneOccT :: FilterE
oneOccT =
  do Let (NonRec v _) body <- id
     guardMsg (varOccCount v body <= 1) "oneOccT: multiple occurrences"

data VarCasts = NoCast | Casts Coercion | FailCast

instance Monoid VarCasts where
  mempty = NoCast
  NoCast   `mappend` c        = c
  c        `mappend` NoCast   = c
  FailCast `mappend` _        = FailCast
  _        `mappend` FailCast = FailCast
  Casts co `mappend` Casts co'
    | co `coreEqCoercion` co' = Casts co
    | otherwise               = FailCast

-- | See if the given variable occurs only with casts having the same coercion.
-- If so, yield that coercion.
castOccsSame :: Var -> CoreExpr -> Maybe Coercion
castOccsSame v e =
  case castOccsSame' v e of
    Casts co -> Just co
    _        -> Nothing

castOccsSame' :: Var -> CoreExpr -> VarCasts
castOccsSame' v = occs
 where
   occs                            :: CoreExpr -> VarCasts
   occs (Var _)                    = mempty
   occs (Lit _)                    = mempty
   occs (App p q)                  = occs p <> occs q
   occs (Lam _ e)                  = occs e  -- assumes no shadowning
   occs (Let b e)                  = bindOccs b <> occs e
   occs (Case e _ _ alts)          = occs e <> foldMap altOccs alts
   occs (Cast (Var u) co) | u == v = Casts co
   occs (Cast e _)                 = occs e
   occs (Tick _ e)                 = occs e
   occs (Type _)                   = mempty
   occs (Coercion _)               = mempty
   altOccs (_,_,e)                 = occs e
   bindOccs (NonRec _ e)           = occs e
   bindOccs (Rec bs)               = foldMap (occs . snd) bs

{--------------------------------------------------------------------
    Borrowed from GHC HEAD >= 7.9
--------------------------------------------------------------------}

-- Converts a coercion to be nominal, if possible.
-- See also Note [Role twiddling functions]
setNominalRole_maybe :: Coercion -> Maybe Coercion
setNominalRole_maybe co
  | Nominal <- coercionRole co = Just co
setNominalRole_maybe (SubCo co)  = Just co
setNominalRole_maybe (Refl _ ty) = Just $ Refl Nominal ty
setNominalRole_maybe (TyConAppCo Representational tc coes)
  = do { cos' <- mapM setNominalRole_maybe coes
       ; return $ TyConAppCo Nominal tc cos' }
setNominalRole_maybe (UnivCo Representational ty1 ty2) = Just $ UnivCo Nominal ty1 ty2
  -- We do *not* promote UnivCo Phantom, as that's unsafe.
  -- UnivCo Nominal is no more unsafe than UnivCo Representational
setNominalRole_maybe (TransCo co1 co2)
  = TransCo <$> setNominalRole_maybe co1 <*> setNominalRole_maybe co2
setNominalRole_maybe (AppCo co1 co2)
  = AppCo <$> setNominalRole_maybe co1 <*> pure co2
setNominalRole_maybe (ForAllCo tv co)
  = ForAllCo tv <$> setNominalRole_maybe co
setNominalRole_maybe (NthCo n co)
  = NthCo n <$> setNominalRole_maybe co
setNominalRole_maybe (InstCo co ty)
  = InstCo <$> setNominalRole_maybe co <*> pure ty
setNominalRole_maybe _ = Nothing

#else

#endif

-- | Succeeds if we are looking at an application of a data constructor.
exprAsConApp :: CoreExpr -> Maybe (DataCon, [Type], [CoreExpr])
exprAsConApp e = exprIsConApp_maybe (in_scope, idUnfolding) e
 where
   in_scope =mkInScopeSet
              (mkVarEnv [ (v,v) | v <- varSetElems (localFreeVarsExpr e) ])

{--------------------------------------------------------------------
    HERMIT utilities
--------------------------------------------------------------------}

newIdT :: String -> TransformM c Type Id
newIdT nm = do ty <- id
               constT (newIdH nm ty)

-- Common context & monad constraints
-- type OkCM c m =
--   ( HasDynFlags m, Functor m, MonadThings m, MonadCatch m
--   , BoundVars c, HasModGuts m )

-- type OkCM c m = 
--   ( BoundVars c, HasDynFlags m, HasHscEnv m, HasHermitMEnv m
--   , Functor m, MonadCatch m, MonadIO m, MonadThings m )

type OkCM c m =
  ( BoundVars c
  , MonadCatch m, MonadIO m, MonadThings m, HasHermitMEnv m, LiftCoreM m
  )

type TransformU b = forall c m a. OkCM c m => Transform c m a b

type TransformM c a b = Transform c HermitM a b
type RewriteM c a = TransformM c a a

-- Apply a named id to type and value arguments.
apps' :: HermitName -> [Type] -> [CoreExpr] -> TransformU CoreExpr
apps' s ts es = (\ i -> apps i ts es) <$> findIdT s

-- Apply a named id to type and value arguments.
apps1' :: HermitName -> [Type] -> CoreExpr -> TransformU CoreExpr
apps1' s ts = apps' s ts . (:[])

type ReType  = RewriteH Type
type ReProg  = RewriteH CoreProg
type ReBind  = RewriteH CoreBind
type ReExpr  = RewriteH CoreExpr
type ReAlt   = RewriteH CoreAlt
type ReCore  = RewriteH Core
type ReLCore = RewriteH LCore
type ReGuts  = RewriteH ModGuts

#if 0

-- | Lookup the name in the context first, then, failing that, in GHC's global
-- reader environment.
findTyConT :: String -> TransformU TyCon
findTyConT nm =
  prefixFailMsg ("Cannot resolve name " ++ nm ++ "; ") $
  contextonlyT (findTyConMG nm)

findTyConMG :: OkCM c m => String -> c -> m TyCon
findTyConMG nm _ =
  do rdrEnv <- mg_rdr_env <$> getModGuts
     case filter isTyConName $ findNamesFromString rdrEnv nm of
       [n] -> lookupTyCon n
       ns  -> do dynFlags <- getDynFlags
                 fail $ show (length ns) 
                      ++ " matches found: "
                      ++ intercalate ", " (showPpr dynFlags <$> ns)

#endif

-- TODO: remove context argument, simplify OkCM, etc. See where it leads.
-- <https://github.com/conal/type-encode/issues/2>

-- TODO: Use findTyConT in HERMIT.Dictionary.Name instead of above.

tcFind :: (TyCon -> b) -> HermitName -> TransformU b
tcFind h = fmap h . findTyConT

tcFind0 :: HermitName -> TransformU Type
tcFind0 = tcFind tcApp0

tcFind2 :: HermitName -> TransformU (Binop Type)
tcFind2 = tcFind tcApp2

callSplitT :: MonadCatch m =>
              Transform c m CoreExpr (CoreExpr, [Type], [CoreExpr])
callSplitT = do (f,args) <- callT
                let (tyArgs,valArgs) = splitTysVals args
                return (f,tyArgs,valArgs)

callNameSplitT :: OkCM c m =>
  HermitName -> Transform c m CoreExpr (CoreExpr, [Type], [Expr CoreBndr])
callNameSplitT name = do (f,args) <- callNameT name
                         let (tyArgs,valArgs) = splitTysVals args
                         return (f,tyArgs,valArgs)

-- TODO: refactor with something like HERMIT's callPredT

-- | Uncall a named function
unCall ::  OkCM c m => HermitName -> Transform c m CoreExpr [CoreExpr]
unCall f = do (_f,_tys,args) <- callNameSplitT f
              return args

-- | Uncall a named function of one value argument, dropping initial type args.
unCall1 :: HermitName -> ReExpr
unCall1 f = do [e] <- unCall f
               return e

mkUnit :: TransformU CoreExpr
mkUnit = return (mkCoreTup [])

mkPair :: TransformU (Binop CoreExpr)
mkPair = return $ \ u v  -> mkCoreTup [u,v]

moduledName :: String -> String -> HermitName
-- moduledName modName = fromString . (modName ++) . ('.' :)
moduledName = mkQualified  -- Now exported from HERMIT.Name

eitherName :: String -> HermitName
eitherName = moduledName "Data.Either"

mkLR :: String -> TransformU (Type -> Type -> Unop CoreExpr)
mkLR name = do f <- findIdT (eitherName name)
               return $ \ tu tv a -> apps f [tu,tv] [a]

mkLeft  :: TransformU (Type -> Type -> Unop CoreExpr)
mkLeft  = mkLR "Left"

mkRight :: TransformU (Type -> Type -> Unop CoreExpr)
mkRight = mkLR "Right"

mkEither :: TransformU (Binop Type)
mkEither = tcFind2 (eitherName "Either")

type InCoreTC t = Injection t LCoreTC

-- Whether we're observing rewrites
type Observing = Bool

observeR' :: (ReadBindings c, ReadCrumb c, LemmaContext c) =>
             Observing -> InCoreTC t => String -> RewriteM c t
observeR' True  = observeR
observeR' False = const idR

tries :: (MonadCatch m, InCoreTC t) =>
         [Rewrite c m t] -> Rewrite c m t
tries = foldr (<+) ({- observeR' "Unhandled" >>> -} fail "unhandled")

triesL :: (ReadBindings c, ReadCrumb c, LemmaContext c, InCoreTC t) =>
          Observing -> [(String,RewriteM c t)] -> RewriteM c t
triesL observing = tries . map (labeled observing)

-- scopeR :: InCoreTC a => String -> Unop (RewriteM c a)
scopeR :: String -> Unop (TransformM c a b)
scopeR label r = traceR ("Try " ++ label ) >>>
                 -- r
                 (r <+ (traceR (label ++ " failed") >>> fail "scopeR"))

labeled :: (ReadBindings c, ReadCrumb c, LemmaContext c, InCoreTC a) =>
           Observing -> (String, RewriteM c a) -> RewriteM c a
labeled observing (label,r) =
  prefixFailMsg (label ++ " failed: ") $
#ifdef WatchFailures
  scopeR label $
#endif
  (if observing then bracketR label else id) r

lintExprR :: (Functor m, Monad m, HasDynFlags m, BoundVars c) =>
             Rewrite c m CoreExpr
-- lintExprR = (id &&& lintExprT) >>> arr fst
lintExprR = lintExprT >> id

#if 0
-- lintExprR = ifM (True <$ lintExprT) id (fail "lint failure")

lintExprDieR :: (Functor m, MonadCatch m, HasDynFlags m, BoundVars c) =>
                Rewrite c m CoreExpr
lintExprDieR = lintExprR `catchM` error

-- lintExprT :: (BoundVars c, Monad m, HasDynFlags m) =>
--              Transform c m CoreExpr String
#endif

-- | Apply a rewrite rule. If it succeeds but the result fails to pass
-- core-lint, show the before and after (via 'bracketR') and die with the
-- core-lint error message.
lintingExprR :: ( ReadBindings c, ReadCrumb c, LemmaContext c
                , BoundVars c, AddBindings c, ExtendCrumb c, HasEmptyContext c  -- for unshadowR
                ) =>
                String -> Unop (Rewrite c HermitM CoreExpr)
lintingExprR msg rr =
  do e  <- idR
     e' <- rr'
     res <- attemptM (lintExprT $* e')
     either (\ lintMsg -> do _ <- bracketR ("Lint check " ++ msg) rr' $* e
                             error ("Lint failure: " ++ lintMsg)
                             -- traceR lintMsg
            )
            (const $ do unless (isType e || isType e') (
                          do let t  = exprType' e 
                                 t' = exprType' e'
                             unless ({- True || -} t `eqType` t') $ -- See 2015-11-27 notes
                               do _ <- bracketR ("Type changed! " ++ msg) rr' $* e
                                  st  <- showPprT $* t
                                  st' <- showPprT $* t'
                                  error (printf "OOPS! Type changed.\n  Old: %s\n  New: %s"
                                          (dropModules st) (dropModules st')))
                        return e')
            res
 where
   rr' = rr >>> extractR (tryR unshadowR)

-- -- Lint both before and after
-- lintingExprR2 :: ( ReadBindings c, ReadCrumb c
--                  , BoundVars c, AddBindings c, ExtendCrumb c, HasEmptyContext c  -- for unshadowR
--                  ) =>
--                  String -> Unop (Rewrite c HermitM CoreExpr)
-- lintingExprR2 msg rr =
--   lintingExprR ("Before " ++ msg) id >> lintingExprR ("After " ++ msg) rr

-- TODO: Compare types before and after.

-- TODO: Eliminate labeled.

-- labeledR' :: InCoreTC a => Bool -> String -> Unop (RewriteH a)
-- labeledR' debug label r =
--   do c <- contextT
--      labeled debug (label,r)

-- mkVarName :: MonadThings m => Transform c m Var (CoreExpr,Type)
-- mkVarName = contextfreeT (mkStringExpr . uqName . varName) &&& arr varType

varLitE :: Var -> CoreExpr
varLitE = Lit . mkMachString . uqVarName

uqVarName :: Var -> String
uqVarName = unqualifiedName . varName

fqVarName :: Var -> String
fqVarName = qualifiedName . varName

-- Fully type-eta-expand, i.e., ensure that every leading forall has a matching
-- (type) lambdas.
typeEtaLong :: ReExpr
typeEtaLong = readerT $ \ e ->
                 if isTyLam e then
                   lamAllR idR typeEtaLong
                 else
                   expand
 where
   -- Eta-expand enough for lambdas to match foralls.
   expand = do e@(collectForalls . exprType' -> (tvs,_)) <- idR
               return $ mkLams tvs (mkApps e ((Type . TyVarTy) <$> tvs))

simplifyE :: ReExpr
simplifyE = extractR simplifyR

walkE :: Unop ReCore -> Unop ReExpr
walkE trav r = extractR (trav (promoteR r :: ReCore))

alltdE, anytdE, anybuE, onetdE, onebuE :: Unop ReExpr
alltdE = walkE alltdR
anytdE = walkE anytdR
anybuE = walkE anybuR
onetdE = walkE onetdR
onebuE = walkE onebuR

-- TODO: Try rewriting more gracefully, testing isForAllTy first and
-- maybeEtaExpandR

isWorkerT :: FilterE
isWorkerT = do Var (isWorker -> True) <- id
               return ()

isWorker :: Id -> Bool
isWorker = ("$W" `isPrefixOf`) . uqVarName

inlineWorkerR :: ReExpr
inlineWorkerR = isWorkerT >> inlineR

-- Apply a rewriter inside type lambdas.
inAppTys :: Unop ReExpr
inAppTys r = r'
 where
   r' = readerT $ \ e -> if isAppTy e then appAllR r' idR else r

isAppTy :: CoreExpr -> Bool
isAppTy (App _ (Type _)) = True
isAppTy _                = False

letFloatToProg :: (BoundVars c, AddBindings c, ReadCrumb c, ExtendCrumb c) =>
                  TransformM c CoreBind CoreProg
letFloatToProg = arr (flip ProgCons ProgNil) >>> tryR letFloatTopR

-- TODO: alias for these c constraints.

concatProgs :: [CoreProg] -> CoreProg
concatProgs = bindsToProg . concatMap progToBinds

-- | Reject if condition holds. Opposite of 'acceptR'
rejectR :: Monad m => (a -> Bool) -> Rewrite c m a
rejectR f = acceptR (not . f)

-- | Reject if condition holds on an expression's type.
rejectTypeR :: Monad m => (Type -> Bool) -> Rewrite c m CoreExpr
rejectTypeR f = rejectR (f . exprType')

-- | Succeed only if the given rewrite actually changes the term
changedSynR :: (MonadCatch m, SyntaxEq a) => Unop (Rewrite c m a)
changedSynR = changedByR (=~=)

-- | Succeed only if the given rewrite actually changes the term
changedArrR :: (MonadCatch m, SyntaxEq a) => Unop a -> Rewrite c m a
changedArrR = changedSynR . arr

-- | Use GHC expression simplifier and succeed if different. Sadly, the check
-- gives false positives, which spoils its usefulness.
simplifyExprR :: ReExpr
simplifyExprR = changedSynR $
  prefixFailMsg "simplify-expr failed: " $
    contextfreeT $ \ e ->
      do dflags <- getDynFlags
         liftIO $ simplifyExpr dflags e

-- | Get a GHC pretty-printing
showPprT :: (HasDynFlags m, Outputable a, Monad m) =>
            Transform c m a String
showPprT = do a <- id
              dynFlags <- constT getDynFlags
              return (showPpr dynFlags a)

-- | Make a stash label out of an outputtable
stashLabel :: (Functor m, Monad m, HasDynFlags m, Outputable a) =>
              Transform c m a String
stashLabel = tweakLabel <$> showPprT

-- Replace whitespace runs with underscores
tweakLabel :: Unop String
tweakLabel = intercalate "_" . words

dropModules :: Unop String
dropModules = unwords . map dropMods . words
 where
   dropMods (c:rest) | not (isUpper c) = c : dropMods rest
   dropMods (break (== '.') -> (_,'.':rest)) = dropMods rest
   dropMods s = s

memoChat :: (ReadBindings c, ReadCrumb c, Injection a CoreTC) =>
            Bool -> String -> String -> RewriteM c a
memoChat brag pre lab =
  if brag then
    chat ("memo " ++ pre ++ ": " ++ lab)
  else
    id
 where
   chat = traceR
          -- observeR

-- Needs work
#if 0

-- | Save a definition for future use.
saveDefT :: (ReadBindings c, AddBindings c, ReadCrumb c, ExtendCrumb c) =>
            Observing -> String -> TransformM c CoreDef ()

saveDefT brag lab =
  do def@(Def _ e) <- id
     rememberR (fromString lab) $* DefCore def
     memoChat brag "save" lab $* e
     return ()

-- saveDefT brag lab =
--   do def@(Def _ e) <- id
--      constT (rememberR (fromString lab) def) >>> (memoChat brag "save" lab $* e >> return ())

findDefT :: (ReadBindings c, ReadCrumb c) =>
            Observing -> String -> TransformM c a CoreExpr
findDefT brag lab =
  unfoldRememberedR NotUsed (fromString lab)
  >>> memoChat brag "hit" lab

-- findDefT brag lab =
--   constT (defExpr <$> unfoldRememberedR NotUsed (fromString lab)) >>> memoChat brag "hit" lab
--  where
--    defExpr (Def _ expr) = expr

saveDefNoFloatT :: (ReadBindings c, AddBindings c, ReadCrumb c, ExtendCrumb c) =>
                   Observing -> String -> TransformM c CoreExpr ()
saveDefNoFloatT brag lab =
  do e <- id
     v <- newIdT bogusDefName $* exprType' e
     saveDefT brag lab $* Def v e

#endif

-- | unJust as transform. Fails on Nothing.
-- Already in Kure?
unJustT :: Monad m => Transform c m (Maybe a) a
unJustT = do Just x <- idR
             return x

-- | GHC's tcView as a rewrite
tcViewT :: RewriteM c Type
tcViewT = unJustT . arr tcView

-- | Dissect a function coercion into role, domain, and range
unFunCo :: Coercion -> Maybe (Role,Coercion,Coercion)
unFunCo (TyConAppCo role tc [domCo,ranCo])
  | isFunTyCon tc = Just (role,domCo,ranCo)
unFunCo _ = Nothing

-- | cast (\ v -> e) (domCo -> ranCo)
--     ==> (\ v' -> cast (e[Var v <- cast (Var v') (SymCo domCo)]) ranCo)
-- where v' :: a' if the whole expression had type a' -> b'.
-- Warning, to avoid looping, don't combine with 'castFloatLamR'.
lamFloatCastR :: ReExpr
lamFloatCastR = -- labelR "lamFloatCastR" $
  do Cast (Lam v e) (unFunCo -> Just (_,domCo,ranCo)) <- idR
     Just (domTy,_) <- arr (splitFunTy_maybe . exprType')
     v' <- constT $ newIdH (uqVarName v) domTy
     let e' = subst [(v, Cast (Var v') (SymCo domCo))] e
     return (Lam v' (Cast e' ranCo))

-- Now in HERMIT. (Did I just not notice earlier?)
-- -- | (\ x :: a -> u `cast` co)  ==>  (\ x -> u) `cast` (<a> -> co)
-- -- Warning, to avoid looping, don't combine with 'lamFloatCastR'.
-- castFloatLamR :: ReExpr
-- castFloatLamR =
--   do Lam x (u `Cast` co) <- id
--      return $
--        Lam x u `mkCast` (mkFunCo repr (mkReflCo repr (varType x)) co)

-- TODO: Should I check the role?

-- | cast (cast e co) co' ==> cast e (mkTransCo co co')
castCastR :: ReExpr
castCastR = -- labelR "castCastR" $
            do Cast (Cast e co) co' <- idR
               return (Cast e (mkTransCo co co'))

-- e `cast` (co1 ; co2)  ==>  (e `cast` co1) `cast` co2
-- Handle with care. Don't mix with its inverse, 'castCastR'.
unCastCastR :: Monad m => Rewrite c m CoreExpr
unCastCastR = do e `Cast` (co1 `TransCo` co2) <- idR
                 return ((e `Cast` co1) `Cast` co2)

-- Collapse transitive coercions when the latter is universal.
-- TODO: Maybe re-associate.
castTransitiveUnivR :: ReExpr
castTransitiveUnivR =
  do Cast e (TransCo (coercionKind -> Pair t _) (UnivCo prov r _ t')) <- id
     return $ mkCast e (mkUnivCo prov r t t')

-- univCoProvHack :: UnivCoProvenance
-- univCoProvHack = PluginProv "plugin-foo"

-- Like 'castFloatAppR', but handles transitivy coercions.
castFloatAppR' :: (MonadCatch m, ExtendCrumb c) =>
                  Rewrite c m CoreExpr
castFloatAppR' = castFloatAppR <+
                 -- castFloatAppUnivR <+
                 (appAllR unCastCastR id >>> castFloatAppR')

-- For now
mkUnivCo' :: Role -> Type -> Type -> Coercion
-- mkUnivCo' = mkUnsafeCo
mkUnivCo' = mkUnivCo (fsLit "plugin-foo-provenance")

-- | Like castFloatApp but handles *all* coercions, and makes universal coercions.
--   (f `cast` (co :: (a -> b) ~ (a' -> b'))) e  ==>
--   f (e `cast` (univ :: a' ~ a)) `cast` (univ :: b ~ b')
-- or
--   (f `cast` (co :: (forall a. b) ~ (forall a. b'))) (Type t)  ==
--   f e `cast` (univ :: [a := t]b ~ [a := t]b')
castFloatAppUnivR :: MonadCatch m => Rewrite c m CoreExpr
castFloatAppUnivR =
  do App (Cast fun co) arg <- id
     let Pair ty ty' = coercionKind co
         role = coercionRole co
     (do Just (a ,b ) <- return $ splitFunTy_maybe ty
         Just (a',b') <- return $ splitFunTy_maybe ty'
         -- guardMsg (a =~= a')
         --   "castFloatAppUnivR: cast changes domain types"
         return $
           mkCast (App fun (mkCast arg (mkUnivCo' role a' a)))
                  (mkUnivCo' role b b'))
      <+
      (do Just (a ,b ) <- return $ splitForAllTy_maybe ty
          Just (a',b') <- return $ splitForAllTy_maybe ty'
          Type tyArg   <- return arg
          guardMsg (a =~= a')
            "castFloatAppUnivR: cast changes type argument"
          return $
            let sub = substTyWith [a] [tyArg] in
              mkCast (App fun arg) (mkUnivCo' role (sub b) (sub b')))

-- | case e of p -> (rhs `cast` co)  ==> (case e of p -> rhs) `cast` co
-- Inverse to 'caseFloatCastR', so don't use both rules!
-- castFloatCaseR :: ReExpr
castFloatCaseR :: MonadCatch m => Rewrite c m CoreExpr
castFloatCaseR =
  do Case scrut wild _ [(con,binds,rhs `Cast` co)] <- id
     return $
       Case scrut wild (pFst (coercionKind co)) [(con,binds,rhs)]
         `Cast` co

-- | Like 'castFloatAppR' but cascades through applications.
castFloatApps :: (MonadCatch m, ExtendCrumb c) => Rewrite c m CoreExpr
castFloatApps = castFloatAppR . (appAllR castFloatApps id <+ id)

-- | Like caseFloatR, but excludes caseFloatCastR, so we can use castFloatCaseR
--   Note: does NOT include caseFloatArg
caseFloatR' :: (ExtendCrumb c, ReadCrumb c, AddBindings c, ReadBindings c) =>
               Rewrite c HermitM CoreExpr
caseFloatR' = setFailMsg "Unsuitable expression for Case floating." $
  caseFloatAppR <+ caseFloatCaseR <+ caseFloatLetR

-- | case scrut of wild t { _ -> body }
--    ==> let wild = scrut in body
-- May be followed by let-elimination.
-- Warning: does not capture GHC's intent to reduce scrut to WHNF.
caseWildR :: ReExpr
caseWildR = -- labeledR "reifyCaseWild" $
  do Case scrut wild _bodyTy [(DEFAULT,[],body)] <- idR
     return $ Let (NonRec wild scrut) body

-- | Like bashExtendedWithR, but for expressions
bashExtendedWithE :: [ReExpr] -> ReExpr
bashExtendedWithE rs = extractR (bashExtendedWithR (promoteR <$> rs))

-- | Like bashUsingR, but for expressions
bashUsingE :: [ReExpr] -> ReExpr
bashUsingE rs = extractR (bashUsingR (promoteR <$> rs))

-- | bashE for expressions
bashE :: ReExpr
bashE = extractR bashR

#if 0
type BashOkay c m = 
  ( AddBindings c, ExtendCrumb c, HasEmptyContext c, LemmaContext c
  , ReadBindings c, ReadCrumb c, MonadCatch m, MonadUnique m )

bashR' :: BashOkay c m => Rewrite c m LCore
bashR' = bashExtendedWithR' []

-- | Like bashExtendedWithE, but replaces case-float-cast with cast-float-case.
-- Having both causes looping.
bashExtendedWithE' :: [ReExpr] -> ReExpr
bashExtendedWithE' rs = extractR (bashExtendedWithR' (promoteR <$> rs))

-- | An extensible bash. Given rewrites are performed before normal bash rewrites.
bashExtendedWithR' :: BashOkay c m
                   => [Rewrite c m LCore] -> Rewrite c m LCore
bashExtendedWithR' rs = bashUsingR (rs ++ map fst bashComponents')

bashComponents' :: BashOkay c m => [(Rewrite c m LCore, String)]
bashComponents' = caseFloats                 -- O(1)
               ++ filter ((/= "case-float-cast") . snd) bashComponents
 where
   caseFloats =
     [ (promoteExprR castFloatCaseR, "cast-float-case")
     , (promoteExprR castFloatAppR , "cast-float-app")
     , (promoteExprR castFloatLamR , "cast-float-lam")
     ]

-- | bashE for expressions
bashE' :: ReExpr
bashE' = extractR bashR'

#endif

-- | Various single-step cast-floating rewrite
castFloat :: ReExpr
castFloat = castFloatAppR <+ castFloatLamR <+ castFloatCaseR
-- TODO: Define castFloatCaseR via caseFloats

type FilterH a = TransformH a ()
type FilterE   = FilterH CoreExpr
type FilterTy  = FilterH Type

-- | Is the expression a type?
isTypeE :: FilterE
isTypeE = typeT successT

-- | Is the expression a cast?
isCastE :: FilterE
isCastE = castT id id mempty

-- | Is the expression a dictionary?
isDictE :: FilterE
isDictE = guardT . (isDictTy <$> exprTypeT)

-- | Is the expression a coercion?
isCoercionE :: FilterE
isCoercionE = coercionT mempty

-- | Like tyConAppT, but for single type argument.
tyConApp1T :: (ExtendCrumb c, Monad m) =>
              Transform c m TyCon a -> Transform c m KindOrType b -> (a -> b -> z)
           -> Transform c m Type z
tyConApp1T ra rb h =
  do TyConApp _ [_] <- id
     tyConAppT ra (const rb) (\ a [b] -> h a b)


modFailMsgM :: MonadCatch m => (String -> m String) -> m a -> m a
modFailMsgM f ma = ma `catchM` (fail <=< f)

setFailMsgM :: MonadCatch m => m String -> m a -> m a
setFailMsgM msgM = modFailMsgM (const msgM)

-- | Like 'buildDictionaryT' but simplifies with 'bashE'.
buildDictionaryT' :: TransformH Type CoreExpr
buildDictionaryT' =
 {- observeR "buildDictionaryT' (pre)" >>> -}
   ( setFailMsgM (("Couldn't build dictionary for "++) <$> showPprT ) $
       tryR bashE . {- scopeR "buildDictionaryT" -} buildDictionaryT )

-- buildDictionaryT' = setFailMsg "Couldn't build dictionary" $
--                     tryR bashE . buildDictionaryT

-- Try again but with multiple type arguments.
simpleDict :: HermitName -> TransformH [Type] CoreExpr
simpleDict name =
  do tc <- findTyConT name
     buildDictionaryT' . arr (TyConApp tc)

-- simpleDict1 :: HermitName -> TransformH Type CoreExpr
-- simpleDict1 name = simpleDict name . arr (:[])

-- | Build and simplify a 'Typeable' instance
buildTypeableT' :: TransformH Type CoreExpr
#if 0
buildTypeableT' =
  do ty <- id
     tc <- findTyConT "Data.Typeable.Typeable"
     buildDictionaryT' $* TyConApp tc [typeKind ty, ty]

-- The findTyConT is failing. Hm!
#else
-- Adapted from buildDictionaryT
buildTypeableT' =
  tryR bashE .
  prefixFailMsg "buildTypeableT failed: " (
    contextfreeT $ \ ty ->
     do (i,bnds) <- buildTypeable ty
        guardMsg (notNull bnds) "no dictionary bindings generated."
        return $ mkCoreLets bnds (varToCoreExpr i) )
#endif

-- | Repeat a rewriter exactly @n@ times.
repeatN :: Monad m => Int -> Unop (Rewrite c m a)
repeatN n = serialise . replicate n

-- | Use in a stashed 'Def' to say that we don't want to dump.
bogusDefName :: String
bogusDefName = "$bogus-def-name$"

dropBogus :: Unop (Map Id CoreExpr)
dropBogus = Map.filterWithKey (\ v _ -> uqVarName v /= bogusDefName)

-- -- | Dump the stash of definitions.
-- dumpStashR :: RewriteH CoreProg
-- dumpStashR = do stashed <- stashIdMapT
--                 already <- arr progBound
--                 let new = dropBogus (Map.difference stashed already)
--                 -- Drop these let bindings from program before extending.
--                 progRhsAnyR (anybuE (dropLets new))  -- or anytdR (repeat (dropLets new))
--                   >>> arr (\ prog -> foldr add prog (Map.toList new))
--  where
--    add (v,rhs) = ProgCons (NonRec v rhs)

-- We only remove let bindings from the top-level of a definition.
-- They get floated there.
-- TODO: Drop unused stashed bindings.

-- dropStashedLetR :: ReExpr
-- dropStashedLetR = stashIdMapT >>= dropLets

-- Rewrite the right-hand sides of top-level definitions
progRhsAnyR :: ReExpr -> RewriteH CoreProg
progRhsAnyR r = progBindsAnyR (const (nonRecOrRecAllR id r))
 where
   nonRecOrRecAllR p q =
     recAllR (const (defAllR p q)) <+ nonRecAllR p q

-- (anybuE (dropLets new))

-- TODO: Handle recursive definition groups also.

-- reifyProg = progBindsT (const (tryR reifyDef >>> letFloatToProg)) concatProgs
-- progBindsAllR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => (Int -> Rewrite c m CoreBind) -> Rewrite c m CoreProg

-- NOTE: I'm converting the stash from a map over RememberedName to a map over Id.
-- Look for a better way.

progBound :: CoreProg -> Map Id CoreExpr
progBound = foldMap bindNames . progToBinds
 where
   bindNames (NonRec v e) = Map.singleton v e
   bindNames (Rec bs)     = Map.fromList bs

-- stashIdMapT :: TransformM c a (Map Id CoreExpr)
-- stashIdMapT =
--   (Map.fromList . Map.elems . fmap defToIdExpr) <$> constT getStash

#if 1

dropLets :: Monad m => Map Id CoreExpr -> Rewrite c m CoreExpr
dropLets defs = dropLetPred (flip Map.member defs)

dropLetPred :: Monad m => (Id -> Bool) -> Rewrite c m CoreExpr
dropLetPred f =
  do Let (NonRec v _) body <- id
     guardMsg (f v) "dropLets: doesn't satisfy predicate"
     return body

#else
-- | Drop a 'let' binding if the variable is already bound. Assumes that the
-- outer matches the inner, but doesn't check. Useful with 'dumpStash'.
dropRedundantLetR :: ReExpr
dropRedundantLetR =
  do Let (NonRec v _) body <- id
     contextonlyT $ \ c ->
       guardMsg (inScope c v) "dropRedundantLet: out of scope"
     return body
#endif

-- Experimental utilities

infixr 8 $*
($*) :: Monad m => Transform c m a b -> a -> Transform c m q b
t $* x = t . return x

pairT :: ReExpr -> ReExpr -> ReExpr
pairT ra rb =
  do [_,_,a,b] <- snd <$> callNameT "GHC.Tuple.(,)"
     liftA2 pair (ra $* a) (rb $* b)
 where
   pair x y = mkCoreTup [x,y]

listT :: Monad m => [Transform c m a b] -> Transform c m [a] [b]
listT rs =
  do es <- id
     guardMsg (length rs == length es) "listT: length mismatch"
     sequence (zipWith ($*) rs es)

unPairR :: OkCM c m => Transform c m CoreExpr (CoreExpr,CoreExpr)
unPairR = do [_,_,a,b] <- snd <$> callNameT "GHC.Tuple.(,)"
             return (a,b)

externC' :: Injection a LCore =>
            ExternalName -> RewriteH a -> External
externC' name rew = externC name rew "not yet documented"

externC :: Injection a LCore =>
           ExternalName -> RewriteH a -> String -> External
externC name rew help =
  external name (promoteR rew :: ReLCore) [help]

-- | Normalize a type, giving coercion and result type.
-- Fails if already normalized (rather than returning 'ReflCo').
normaliseTypeT :: (MonadIO m, HasHermitMEnv m, LiftCoreM m) =>
                  Role -> Transform c m Type (Coercion, Type)
normaliseTypeT r = do
  envs <- constT $
    do guts <- getModGuts
       eps <- getHscEnv >>= liftIO . hscEPS 
       return (eps_fam_inst_env eps, mg_fam_inst_env guts) 
  res@(co,_) <- arr (normaliseType envs r)
  guardMsg (not (isReflCo co)) "normaliseTypeT: already normal"
  return res

-- Adapted from Andrew Farmer's code.

-- | Alias for 'normalizeTypeT'.
normalizeTypeT :: (MonadIO m, HasHermitMEnv m, LiftCoreM m) =>
                  Role -> Transform c m Type (Coercion, Type)
normalizeTypeT = normaliseTypeT

-- | Optimize a coercion.
optimizeCoercionR :: RewriteM c Coercion
optimizeCoercionR = changedArrR (optCoercion emptyCvSubst)

-- | Optimize a cast.
optimizeCastR :: ExtendCrumb c => RewriteM c CoreExpr
optimizeCastR = castAllR id optimizeCoercionR

-- | x = (let y = e in y)  ==>  x = e
bindUnLetIntroR :: ReBind
bindUnLetIntroR =
  do NonRec x (Let (NonRec y e) (Var ((== y) -> True))) <- id
     return (NonRec x e)

-- Now in HERMIT
#if 0

-- | Float a let out of a case alternative:
-- 
--   case foo of { ... ; p -> let x = u in v ; ... }  ==>
--   let x = u in case foo of { ... ; p -> v ; ... }
-- 
-- where no variable in `p` occurs freely in `u`, and where `x` is not one of
-- the variables in `p`.
letFloatCaseAltR :: ReExpr
letFloatCaseAltR =
  do Case scrut w ty alts <- id
     (b,alts') <- letFloatOneAltR alts
     return $ Let b (Case scrut w ty alts')

-- Perform the first safe let-floating out of a case alternative
letFloatOneAltR :: [CoreAlt] -> TransformH x (CoreBind,[CoreAlt])
letFloatOneAltR [] = fail "no alternatives safe to let-float"
letFloatOneAltR (alt:rest) =
  (do (bind,alt') <- letFloatAltR alt
      return (bind,alt':rest))
  <+
  (second (alt :) <$> letFloatOneAltR rest)

-- (p -> let bind in e) ==>  (bind, p -> e)
letFloatAltR :: CoreAlt -> TransformH x (CoreBind,CoreAlt)
letFloatAltR (con,vs,Let bind@(NonRec x a) body)
  | isEmptyVarSet (vset `intersectVarSet` freeVarsExpr a)
    && not (x `elemVarSet` vset)
  = return (bind,(con,vs,body))
 where
   vset = mkVarSet vs
letFloatAltR _ = fail "letFloatAltR: not applicable"

-- TODO: consider variable occurrence conditions more carefully

#endif

{--------------------------------------------------------------------
    Triviality
--------------------------------------------------------------------}

-- exprIsTrivial :: CoreExpr -> Bool
-- exprIsTrivial (Var {})     = True
-- exprIsTrivial (Lit {})     = True
-- exprIsTrivial (App {})     = False
-- exprIsTrivial (Lam _ e)    = exprIsTrivial e
-- exprIsTrivial (Case {})    = False
-- exprIsTrivial (Cast e _)   = exprIsTrivial e
-- exprIsTrivial (Tick _ e)   = exprIsTrivial e
-- exprIsTrivial (Type {})    = True
-- exprIsTrivial (Coercion _) = True

-- Instead use exprIsTrivial from GHC's CoreUtils

-- | Trivial expression: for now, literals, variables, casts of trivial.
trivialExpr :: FilterE
trivialExpr = setFailMsg "Non-trivial" $
              isTypeE <+ isVarT <+ isCoercionE <+ isDictE <+ isLitT
           <+ trivialLam
           <+ castT trivialExpr id mempty

-- TODO: Maybe use a guardM variant and GHC's exprIsTrivial

trivialBind :: FilterH CoreBind
trivialBind = nonRecT successT trivialExpr mempty

trivialLet :: FilterE
trivialLet = letT trivialBind successT mempty

trivialLam :: FilterE
trivialLam = lamT id trivialExpr mempty

trivialBetaRedex :: FilterE
trivialBetaRedex = appT trivialLam successT mempty

-- These filters could instead be predicates. Then use acceptR.

letSubstTrivialR :: ReExpr
letSubstTrivialR = -- watchR "trivialLet" $
                   trivialLet >> letSubstR

betaReduceTrivialR :: ReExpr
betaReduceTrivialR = -- watchR "betaReduceTrivialR" $
                     trivialBetaRedex >> betaReduceR

{--------------------------------------------------------------------
    Case alternative pruning
--------------------------------------------------------------------}

type InTvM a = TvSubst -> a

type ReTv a = a -> InTvM a

pruneBound :: Var -> Unop TvSubst
pruneBound v =
  fromMaybe (error "pruneBound: contradiction") . extendTvSubstVar v

extendTvSubstVar :: Var -> InTvM (Maybe TvSubst)
extendTvSubstVar v | isCoVar v && coVarRole v == Nominal =
                      extendTvSubstTys (coVarKind v)
                   | otherwise = pure

extendTvSubstVars :: [Id] -> TvSubst -> Maybe TvSubst
extendTvSubstVars = foldr (\ v q -> q <=< extendTvSubstVar v) pure

extendTvSubstTys :: (Type,Type) -> TvSubst -> Maybe TvSubst
extendTvSubstTys (a,b) sub =
  unionTvSubst sub <$> tcUnifyTy (substTy sub a) (substTy sub b)

-- TODO: Can I really use unionTvSubst here? Note comment "Works when the ranges
-- are disjoint"

-- TODO: Maybe use normaliseType and check that the resulting coercion is
-- nominal TODO: Handle Representational coercions?

#if 0

pruneAltsR :: ReExpr
pruneAltsR = changedArrR (flip pruneAltsExpr emptyTvSubst)

pruneAltsExpr :: ReTv CoreExpr
pruneAltsExpr e@(Var _)      = pure e
pruneAltsExpr e@(Lit _)      = pure e
pruneAltsExpr (App u v)      = liftA2 App (pruneAltsExpr u) (pruneAltsExpr v)
pruneAltsExpr (Lam x e)      = Lam x <$> (pruneAltsExpr e . pruneBound x)
pruneAltsExpr (Let b e)      = liftA2 Let (pruneAltsBind b) (pruneAltsExpr e)
pruneAltsExpr (Case e w ty alts) =
  Case <$> (pruneAltsExpr e)
       <*> pure w
       <*> pure ty
       <*> (catMaybes <$> mapM pruneAltsAlt alts)
pruneAltsExpr (Cast e co)    = Cast <$> pruneAltsExpr e <*> pure co
pruneAltsExpr (Tick t e)     = Tick t <$> pruneAltsExpr e
pruneAltsExpr e@(Type _)     = pure e
pruneAltsExpr e@(Coercion _) = pure e

pruneAltsBind :: ReTv CoreBind
pruneAltsBind (NonRec x e) = NonRec x <$> (pruneAltsExpr e . pruneBound x)
pruneAltsBind (Rec ves)    =
  \ env -> Rec ((fmap.second) (flip pruneAltsExpr env) ves)

-- For Rec, I'm not gathering any info about the variables, so some pruning may
-- be missed. TODO: Reconsider.
-- TODO: Use an applicative or monadic style for Rec.

pruneAltsAlt :: CoreAlt -> InTvM (Maybe CoreAlt)
pruneAltsAlt (con,vs0,e) =
--   \ env -> case prune vs0 env of
--              Nothing -> Nothing
--              Just env' -> Just (con,vs0,pruneAltsExpr e env')
  (fmap.fmap) ((con,vs0,) . pruneAltsExpr e) (extendTvSubstVars vs0)

-- I think I'll want to combine pruneBound and consistentVar, yielding a Maybe
-- TvSubst. What do I do for pruneAltsExpr etc if a lambda binding proves
-- impossible? What about a let binding?

#else

{--------------------------------------------------------------------
    Type localization
--------------------------------------------------------------------}

-- Eliminate type variables determined by coercions, so that other
-- transformations can use local information.
-- Subsumes pruneAlt*

-- TODO: Make retypeFoo into a class

-- TODO: Still needed?

retypeExprR :: ReExpr
retypeExprR = changedArrR (flip retypeExpr emptyTvSubst)

retypeType :: ReTv Type
retypeType = flip substTy

retypeVar :: ReTv Var
retypeVar x = \ sub -> setVarType x (substTy sub (varType x))

retypeExpr :: ReTv CoreExpr
-- retypeExpr (Var x)        = Var . retypeVar x
retypeExpr (Var x)        = \ sub -> let ty  = varType x
                                         ty' = substTy sub ty
                                     in
                                       mkCast (Var x) (mkUnivCo' Representational ty ty')
retypeExpr e@(Lit _)      = pure e
retypeExpr (App u v)      = App <$> retypeExpr u <*> retypeExpr v
-- retypeExpr (Lam x e)      = Lam <$> retypeVar x <*> (retypeExpr e . pruneBound x)
retypeExpr (Lam x e)      = Lam x <$> retypeExpr e
retypeExpr (Let b e)      = Let <$> retypeBind b <*> retypeExpr e
retypeExpr (Case e w ty alts) =
  Case <$> retypeExpr e
       <*> retypeVar w
       <*> retypeType ty
       <*> (catMaybes <$> mapM retypeAlt alts)
retypeExpr (Cast e co)    = mkCast <$> retypeExpr e <*> retypeCoercion co
retypeExpr (Tick t e)     = Tick t <$> retypeExpr e
retypeExpr (Type t)       = Type <$> retypeType t
retypeExpr (Coercion co)  = Coercion <$> retypeCoercion co

retypeBind :: ReTv CoreBind
retypeBind (NonRec x e) = NonRec <$> retypeVar x <*> (retypeExpr e . pruneBound x)
retypeBind (Rec ves)    =
  Rec <$> mapM (\ (x,e) -> (,) <$> retypeVar x <*> retypeExpr e) ves

-- retypeAlt :: CoreAlt -> InTvM (Maybe CoreAlt)
-- retypeAlt (con,vs0,e) = go vs0 []
--  where
--    go :: [Var] -> [Var] -> TvSubst -> Maybe (CoreAlt)
--    go []     acc sub = return (con, reverse acc, retypeExpr e sub)
--    go (v:vs) acc sub | isCoVar v && coVarRole v == Nominal
--                        = extendTvSubstTys (coVarKind v) sub >>= go vs (v:acc)
--                      | otherwise
--                        = go vs (retypeVar v sub : acc) sub

-- -- Gather substitutions for all of coercion variables.
-- -- Then substitute in the parameters and the body.
-- retypeAlt :: CoreAlt -> InTvM (Maybe CoreAlt)
-- retypeAlt (con,vs,e) sub =
--    do sub' <- extendTvSubstVars vs sub
--       return (con, tyToPat (lookupTvSubst sub') <$> vs, retypeExpr e sub')

-- Gather substitutions for all of coercion variables.
-- Then substitute in the the body.
retypeAlt :: CoreAlt -> InTvM (Maybe CoreAlt)
retypeAlt (con,vs,e) sub =
   do sub' <- extendTvSubstVars vs sub
      return (con, vs, retypeExpr e sub')

-- retypeAlt (con,vs,e) sub =
--    extendTvSubstVars vs sub >>=
--    (con,,) <$> mapM retypeVar vs <*> retypeExpr e

-- TODO: Consider coercions in let and lambda.

-- For now, convert coercions to universal.
retypeCoercion :: ReTv Coercion
retypeCoercion co =
    -- optCoercion emptyCvSubst <$>
    (mkUnivCo' (coercionRole co) <$> retypeType ty <*> retypeType ty')
 where
   Pair ty ty' = coercionKind co

#endif

{--------------------------------------------------------------------
    Balanced binary trees, for type constructions
--------------------------------------------------------------------}

-- Binary leaf tree. Used to construct balanced nested sum and product types.
data Tree a = Empty | Leaf a | Branch (Tree a) (Tree a)
  deriving (Show,Functor,Foldable)

toTree :: [a] -> Tree a
toTree []  = Empty
toTree [a] = Leaf a
toTree xs  = Branch (toTree l) (toTree r)
 where
   (l,r) = splitAt (length xs `div` 2) xs

foldMapT :: b -> (a -> b) -> Binop b -> Tree a -> b
foldMapT e l b = h
 where
   h Empty        = e
   h (Leaf a)     = l a
   h (Branch u v) = b (h u) (h v)

foldT :: a -> Binop a -> Tree a -> a
foldT e b = foldMapT e id b

{--------------------------------------------------------------------
    Syntactic equality
--------------------------------------------------------------------}

-- Syntactic equality tests, taking care to check var types for change.

infix 4 =~=
class SyntaxEq a where
  (=~=) :: a -> a -> Bool

instance (SyntaxEq a, SyntaxEq b) => SyntaxEq (a,b) where
  (a,b) =~= (a',b') = a =~= a' && b =~= b'

instance (SyntaxEq a, SyntaxEq b, SyntaxEq c) => SyntaxEq (a,b,c) where
  (a,b,c) =~= (a',b',c') = a =~= a' && b =~= b' && c =~= c'

instance SyntaxEq a => SyntaxEq [a] where (=~=) = all2 (=~=)

instance SyntaxEq Var      where (=~=) = varSyntaxEq'

varSyntaxEq' :: Var -> Var -> Bool
varSyntaxEq' x y = x == y && varType x =~= varType y

instance SyntaxEq CoreProg where
  ProgNil =~= ProgNil                   = True
  ProgCons bnd1 p1 =~= ProgCons bnd2 p2 = bnd1 =~= bnd2 && p1 =~= p2
  _  =~= _                              = False

instance SyntaxEq CoreBind where
  NonRec v1 e1 =~= NonRec v2 e2 = v1 =~= v2 && e1 =~= e2
  Rec ies1     =~= Rec ies2     = ies1 =~= ies2
  _            =~= _            = False

instance SyntaxEq CoreDef  where
  Def i1 e1 =~= Def i2 e2 = i1 =~= i2 && e1 =~= e2

instance SyntaxEq CoreExpr where
  Var x =~= Var y = x =~= y
  Lit l1             =~= Lit l2             = l1 == l2
  App f1 e1          =~= App f2 e2          = f1 =~= f2 && e1 =~= e2
  Lam v1 e1          =~= Lam v2 e2          = v1 == v2 && e1 =~= e2
  Let b1 e1          =~= Let b2 e2          = b1 =~= b2 && e1 =~= e2
  Case s1 w1 ty1 as1 =~= Case s2 w2 ty2 as2 =
    w1 == w2 && s1 =~= s2 && all2 (=~=) as1 as2 && ty1 =~= ty2
  Cast e1 co1        =~= Cast e2 co2        = e1 =~= e2 && co1 =~= co2
  Tick t1 e1         =~= Tick t2 e2         = t1 == t2 && e1 =~= e2
  Type ty1           =~= Type ty2           = ty1 =~= ty2
  Coercion co1       =~= Coercion co2       = co1 =~= co2
  _                  =~= _                  = False

instance SyntaxEq AltCon   where (=~=) = (==)
instance SyntaxEq Type     where (=~=) = typeSyntaxEq
instance SyntaxEq Coercion where (=~=) = coercionSyntaxEq

regularizeType :: Unop Type
regularizeType (coreView -> Just ty) = regularizeType ty
regularizeType ty@(TyVarTy _)        = ty
regularizeType (AppTy u v)           = AppTy (regularizeType u) (regularizeType v)
regularizeType (TyConApp tc tys)     = TyConApp tc (regularizeType <$> tys)
regularizeType (FunTy u v)           = FunTy (regularizeType u) (regularizeType v)
regularizeType (ForAllTy x ty)       = ForAllTy x (regularizeType ty)
regularizeType ty@(LitTy _)          = ty

cseGuts :: ReGuts
cseGuts = arr (\ guts -> guts { mg_binds = cseProgram (mg_binds guts) })

cseProg :: ReProg
cseProg = arr (bindsToProg . cseProgram . progToBinds)

cseBind :: ReBind
cseBind = arr (head . cseProgram . (:[]))

cseExpr :: ReExpr
cseExpr = do v <- newIdT "cse_dummy" . exprTypeT
             arr (\ (NonRec _ e) -> e) . cseBind . arr (NonRec v)

-- Oops. My CSE transformations always succeed, even when no CSE happens.
-- TODO: Fix.

betaReduceSafePlusR :: MonadCatch m => Rewrite c m CoreExpr
betaReduceSafePlusR = prefixFailMsg "Multi-beta-reduction failed: " $ do
    (f,args) <- callT
    let (e',atLeastOne) = reduceAll f args
        reduceAll (Lam v body) (a:as) =
          (Let (NonRec v a) (fst $ reduceAll body as), True)
        reduceAll e            as     = (mkCoreApps e as, False)
    guardMsg atLeastOne "no beta reductions possible."
    return e'

{--------------------------------------------------------------------
    Copied and altered from HERMIT
--------------------------------------------------------------------}

-- From `HERMIT.Dictionary.Local.Let`:

-- Change criterion (B):
-- 
-- (B) The let-bound value is either:
--       (i)   a variable;
--       (ii)  polymorphic;
--       (iii) dictionary-ish

-- | Variant of 'letNonRecSubstSafeR' accepting a test for whether an expression
-- is simple enough to replicate.
letNonRecSubstSafeR' :: forall c m. 
   ( AddBindings c, ExtendPath c Crumb, ReadPath c Crumb, ReadBindings c
   , HasEmptyContext c, MonadCatch m)
  => Transform c m CoreExpr Bool -> Rewrite c m CoreExpr
letNonRecSubstSafeR' safeBindT =
    do Let (NonRec v _) _ <- idR
       when (isId v) $ guardMsgM (safeSubstT v) "safety criteria not met."
       letNonRecSubstR
  where
    safeSubstT :: Id -> Transform c m CoreExpr Bool
    safeSubstT i = letNonRecT mempty safeBindT (safeOccursT i) (\ () -> (||))

    safeOccursT :: Id -> Transform c m CoreExpr Bool
    safeOccursT i =
      do depth <- varBindingDepthT i
         let occursHereT :: Transform c m Core ()
             occursHereT = promoteExprT (exprIsOccurrenceOfT i depth >>> guardT)

             -- lamOccurrenceT can only fail if the expression is not a Lam
             -- return either 2 (occurrence) or 0 (no occurrence)
             lamOccurrenceT :: Transform c m CoreExpr (Sum Int)
             lamOccurrenceT =  lamT mempty
                                    (mtryM (Sum 2 <$ extractT (onetdT occursHereT)))
                                    mappend

             occurrencesT :: Transform c m Core (Sum Int)
             occurrencesT = prunetdT (promoteExprT lamOccurrenceT <+ (Sum 1 <$ occursHereT))

         extractT occurrencesT >>^ (getSum >>> (< 2))


simplifyR' :: ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c, LemmaContext c, ReadBindings c, ReadPath c Crumb
             , MonadCatch m, MonadUnique m )
          => Transform c m CoreExpr Bool -> Rewrite c m LCore
simplifyR' safeBindT = setFailMsg "Simplify failed: nothing to simplify." $
    innermostR (   promoteBindR recToNonrecR
                <+ promoteExprR ( unfoldBasicCombinatorR
                               <+ betaReducePlusR
                               <+ letNonRecSubstSafeR' safeBindT
                               <+ caseReduceR False
                               <+ letElimR )
               )
