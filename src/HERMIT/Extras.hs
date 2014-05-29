{-# LANGUAGE CPP, Rank2Types, ConstraintKinds, PatternGuards, ViewPatterns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable, TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-} -- see below
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

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
  , isType, exprType',exprTypeT, pairTy
  , tcFind0, tcFind, tcFind2
  , tcApp0, tcApp1, tcApp2
  , isPairTC, isPairTy, isEitherTy, isUnitTy, isBoolTy
  , unliftedType
  , apps, apps', apps1', callSplitT, callNameSplitT, unCall, unCall1
  , collectForalls, subst, isTyLam, setNominalRole_maybe
  , isVarT, isLitT
    -- * HERMIT utilities
  , newIdT
  , liftedKind, unliftedKind
  , ReType, ReExpr, ReCore, FilterC, FilterE, FilterTy, OkCM, TransformU
  , findTyConT, isTypeE, tyConApp1T
  , mkUnit, mkPair, mkLeft, mkRight, mkEither
  , InCoreTC
  , Observing, observeR', tries, triesL, labeled, labeledR
  , lintExprR -- , lintExprDieR
  , lintingExprR
  , varLitE, uqVarName, fqVarName, typeEtaLong, simplifyE
  , anytdE, anybuE, inAppTys , isAppTy
  , letFloatToProg
  , concatProgs
  , rejectR , rejectTypeR
  , simplifyExprR, whenChangedR
  , showPprT
  , externC', externC
  , unJustT, tcViewT, unFunCo
  , lamFloatCastR, castCastR, unCastCastR, castFloatAppR', castFloatCaseR, caseFloatR'
  , caseWildR
  , bashExtendedWithE, bashUsingE, bashE
  , buildDictionaryT'
  , CustomC(..), TransformM,RewriteM, TransformC,RewriteC, onHermitC, projectHermitC, debugR -- , liftCustomC
  , repeatN
  , saveDefNoFloat, dumpStashR, dropStashedLetR
  , progRhsAnyR -- , dropLetPred -- REMOVE
  , ($*), pairT, listT, pairCastR
  ) where

import Prelude hiding (id,(.))

import Control.Category (Category(..),(>>>))
import Data.Functor ((<$>),(<$))
import Data.Foldable (foldMap)
import Control.Applicative (Applicative(..),liftA2)
import Control.Arrow (Arrow(..))
import Data.List (intercalate)
import Text.Printf (printf)
import Data.Typeable (Typeable)
import Control.Monad.IO.Class (MonadIO)
import Data.Map (Map)
import qualified Data.Map as Map

-- GHC
import Unique(hasKey)
import PrelNames (
  liftedTypeKindTyConKey,unliftedTypeKindTyConKey,constraintKindTyConKey,
  eitherTyConName)
import SimplCore (simplifyExpr)
import qualified Coercion

-- import Language.KURE.Transform (apply)
import HERMIT.Core
  ( CoreProg(..),Crumb,bindsToProg,progToBinds
  , exprAlphaEq,CoreDef(..),defToIdExpr )
import HERMIT.Monad (HermitM,HasModGuts(..),HasHscEnv(..),newIdH,Label,saveDef,getStash)
import HERMIT.Context
  ( BoundVars(..),AddBindings(..),ReadBindings(..)
  , HasEmptyContext(..), HasCoreRules(..)
  , HermitC )
-- Note that HERMIT.Dictionary re-exports HERMIT.Dictionary.*
import HERMIT.Dictionary
  ( findIdT, callT, callNameT, simplifyR, letFloatTopR
  , observeR, bracketR, bashExtendedWithR, bashUsingR, bashR, wrongExprForm
  , castFloatAppR
  , caseFloatCastR, caseFloatCaseR, caseFloatAppR, caseFloatLetR
  , unshadowR, lintExprT, buildDictionaryT, inScope
#ifdef WatchFailures
  , traceR
#endif
  )
-- import HERMIT.Dictionary (traceR)
import HERMIT.GHC hiding (FastString(..))
import HERMIT.Kure hiding (apply)
import HERMIT.External (External,Extern(..),external,ExternalName)

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

-- Form an application to type and value arguments.
apps :: Id -> [Type] -> [CoreExpr] -> CoreExpr
apps f ts es
  | tyArity f /= length ts =
      error $ printf "apps: Id %s wants %d type arguments but got %d."
                     (var2String f) arity ntys
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
     return (exprType e)

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

isUnitTy :: Type -> Bool
isUnitTy (TyConApp tc []) = tc == unitTyCon
isUnitTy _                = False

isBoolTy :: Type -> Bool
isBoolTy (TyConApp tc []) = tc == boolTyCon
isBoolTy _                = False

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

#if __GLASGOW_HASKELL__ < 709

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

type OkCM c m = 
  ( BoundVars c, Functor m, HasDynFlags m, HasModGuts m, HasHscEnv m
  , MonadCatch m, MonadIO m, MonadThings m )

type TransformU b = forall c m a. OkCM c m => Transform c m a b

type TransformM c a b = Transform c HermitM a b
type RewriteM c a = TransformM c a a

-- Apply a named id to type and value arguments.
apps' :: String -> [Type] -> [CoreExpr] -> TransformU CoreExpr
apps' s ts es = (\ i -> apps i ts es) <$> findIdT s

-- Apply a named id to type and value arguments.
apps1' :: String -> [Type] -> CoreExpr -> TransformU CoreExpr
apps1' s ts = apps' s ts . (:[])

type ReType = RewriteC Type
type ReExpr = RewriteC CoreExpr
type ReCore = RewriteC Core

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

-- TODO: remove context argument, simplify OkCM, etc. See where it leads.
-- <https://github.com/conal/type-encode/issues/2>

-- TODO: Use findTyConT in HERMIT.Dictionary.Name instead of above.

tcFind :: (TyCon -> b) -> String -> TransformU b
tcFind h = fmap h . findTyConT

tcFind0 :: String -> TransformU Type
tcFind0 = tcFind tcApp0

tcFind2 :: String -> TransformU (Binop Type)
tcFind2 = tcFind tcApp2

callSplitT :: MonadCatch m =>
              Transform c m CoreExpr (CoreExpr, [Type], [CoreExpr])
callSplitT = do (f,args) <- callT
                let (tyArgs,valArgs) = splitTysVals args
                return (f,tyArgs,valArgs)

callNameSplitT :: MonadCatch m => String
               -> Transform c m CoreExpr (CoreExpr, [Type], [Expr CoreBndr])
callNameSplitT name = do (f,args) <- callNameT name
                         let (tyArgs,valArgs) = splitTysVals args
                         return (f,tyArgs,valArgs)

-- TODO: refactor with something like HERMIT's callPredT

-- | Uncall a named function
unCall :: MonadCatch m =>
          String -> Transform c m CoreExpr [CoreExpr]
unCall f = do (_f,_tys,args) <- callNameSplitT f
              return args

-- | Uncall a named function of one argument
unCall1 :: String -> ReExpr
unCall1 f = do [e] <- unCall f
               return e

mkUnit :: TransformU CoreExpr
mkUnit = return (mkCoreTup [])

mkPair :: TransformU (Binop CoreExpr)
mkPair = return $ \ u v  -> mkCoreTup [u,v]

eitherName :: Unop String
eitherName = ("Data.Either." ++)

mkLR :: String -> TransformU (Type -> Type -> Unop CoreExpr)
mkLR name = do f <- findIdT (eitherName name)
               return $ \ tu tv a -> apps f [tu,tv] [a]

mkLeft  :: TransformU (Type -> Type -> Unop CoreExpr)
mkLeft  = mkLR "Left"

mkRight :: TransformU (Type -> Type -> Unop CoreExpr)
mkRight = mkLR "Right"

mkEither :: TransformU (Binop Type)
mkEither = tcFind2 (eitherName "Either")

type InCoreTC t = Injection t CoreTC

-- Whether we're observing rewrites
type Observing = Bool

observeR' :: (ReadBindings c, ReadCrumb c) =>
             Observing -> InCoreTC t => String -> RewriteM c t
observeR' True  = observeR
observeR' False = const idR

tries :: (MonadCatch m, InCoreTC t) =>
         [Rewrite c m t] -> Rewrite c m t
tries = foldr (<+) ({- observeR' "Unhandled" >>> -} fail "unhandled")

triesL :: (ReadBindings c, ReadCrumb c, InCoreTC t) =>
          Observing -> [(String,RewriteM c t)] -> RewriteM c t
triesL observing = tries . map (labeled observing)

#ifdef WatchFailures
scopeR :: InCoreTC a => String -> Unop (RewriteM c a)
scopeR label r = traceR ("Try " ++ label ) >>>
                 -- r
                 (r <+ (traceR (label ++ " failed") >>> fail "scopeR"))
#endif

labeled :: (ReadBindings c, ReadCrumb c, InCoreTC a) =>
           Observing -> (String, RewriteM c a) -> RewriteM c a
labeled observing (label,r) =
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
lintingExprR :: ( ReadBindings c, ReadCrumb c
                , BoundVars c, AddBindings c, ExtendCrumb c, HasEmptyContext c  -- for unshadowR
                ) =>
                String -> Unop (Rewrite c HermitM CoreExpr)
lintingExprR msg rr =
  do e  <- idR
     e' <- rr'
     res <- attemptM (return e' >>> lintExprT)
     either (\ lintMsg -> return e >>>
                          bracketR msg rr' >>>
                          error lintMsg)
            (const (return e'))
            res
 where
   rr' = rr >>> extractR (tryR unshadowR)

-- TODO: Eliminate labeled.

labeledR :: InCoreTC a => String -> Unop (RewriteC a)
labeledR label r =
  do c <- contextT
     labeled (cDebugFlag c) (label,r)

-- mkVarName :: MonadThings m => Transform c m Var (CoreExpr,Type)
-- mkVarName = contextfreeT (mkStringExpr . uqName . varName) &&& arr varType

varLitE :: Var -> CoreExpr
varLitE = Lit . mkMachString . uqVarName

uqVarName :: Var -> String
uqVarName = uqName . varName

fqVarName :: Var -> String
fqVarName = fqName . varName

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
   expand = do e@(collectForalls . exprType -> (tvs,_)) <- idR
               return $ mkLams tvs (mkApps e ((Type . TyVarTy) <$> tvs))

simplifyE :: ReExpr
simplifyE = extractR simplifyR

anytdE :: Unop ReExpr
anytdE r = extractR (anytdR (promoteR r :: ReCore))

anybuE :: Unop ReExpr
anybuE r = extractR (anybuR (promoteR r :: ReCore))

-- TODO: Try rewriting more gracefully, testing isForAllTy first and
-- maybeEtaExpandR

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
rejectTypeR f = rejectR (f . exprType)

-- | Succeed only if the given rewrite actually changes the 
whenChangedR :: String -> (a -> a -> Bool) -> Unop (RewriteM c a)
whenChangedR name eq r =
  do (e,e') <- (r &&& idR)
     guardMsg (not (eq e e'))
      (name ++ ": result is unchanged from input.")
     return e'

-- TODO: Replace whenChangedR with changedByR from KURE.Combinators.Transform.

-- | Use GHC expression simplifier and succeed if different. Sadly, the check
-- gives false positives, which spoils its usefulness.
simplifyExprR :: ReExpr
simplifyExprR =
  whenChangedR "simplify-expr" exprAlphaEq $
    prefixFailMsg "simplify-expr failed: " $
      contextfreeT $ \ e ->
        do dflags <- getDynFlags
           liftIO $ simplifyExpr dflags e

-- TODO: Try exprSyntaxEq from HERMIT.Core:
-- 
-- exprSyntaxEq :: CoreExpr -> CoreExpr -> Bool

-- TODO: Maybe an EQ-like type class for comparisons.

-- | Get a GHC pretty-printing
showPprT :: (HasDynFlags m, Outputable a, Monad m) =>
            Transform c m a String
showPprT = do a <- id
              dynFlags <- constT getDynFlags
              return (showPpr dynFlags a)

#if 0
externC :: forall c m a.
           (Monad m, Injection a Core, Extern (Rewrite c m Core)) =>
           ExternalName -> Rewrite c m a -> String -> External
externC name rew help =
  external name (promoteR rew :: Rewrite c m Core) [help]
#endif

externC' :: Injection a Core =>
            Bool -> ExternalName -> RewriteC a -> String -> External
externC' dbg name rew help =
  external name (promoteR (debugR dbg rew) :: RewriteH Core) [help]

externC :: Injection a Core =>
           ExternalName -> RewriteC a -> String -> External
externC = externC' False

-- OOPS. Not what I want, since it turns on debugging when the command is
-- defined. I want to turn it on dynamically.

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
lamFloatCastR :: ReExpr
lamFloatCastR = -- labelR "lamFloatCastR" $
  do Cast (Lam v e) (unFunCo -> Just (_,domCo,ranCo)) <- idR
     Just (domTy,_) <- arr (splitFunTy_maybe . exprType')
     v' <- constT $ newIdH (uqVarName v) domTy
     let e' = subst [(v, Cast (Var v') (SymCo domCo))] e
     return (Lam v' (Cast e' ranCo))

-- TODO: Should I check the role?

-- | cast (cast e co) co' ==> cast e (mkTransCo co co')
castCastR :: ReExpr
castCastR = -- labelR "castCastR" $
            do (Cast (Cast e co) co') <- idR
               return (Cast e (mkTransCo co co'))

-- e `cast` (co1 ; co2)  ==>  (e `cast` co1) `cast` co2
-- Handle with care. Don't mix with its inverse, 'castCastR'.
unCastCastR :: Monad m => Rewrite c m CoreExpr
unCastCastR = do e `Cast` (co1 `TransCo` co2) <- idR
                 return ((e `Cast` co1) `Cast` co2)

-- Like 'castFloatAppR', but handles transitivy coercions.
castFloatAppR' :: (MonadCatch m, ExtendCrumb c) =>
                  Rewrite c m CoreExpr
castFloatAppR' = castFloatAppR <+
                 (appAllR unCastCastR id >>> castFloatAppR')

-- | case e of p -> (rhs `cast` co)  ==> (case e of p -> rhs) `cast` co
-- Inverse to 'caseFloatCastR', so don't use both rules!
castFloatCaseR :: ReExpr
castFloatCaseR =
  do Case scrut wild _ [(con,binds,rhs `Cast` co)] <- id
     return $
       Case scrut wild (pFst (coercionKind co)) [(con,binds,rhs)]
         `Cast` co

-- | Like caseFloatR, but excludes caseFloatCastR, so we can use castFloatCaseR
--   Note: does NOT include caseFloatArg
caseFloatR' :: (ExtendCrumb c, ReadCrumb c, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseFloatR' = setFailMsg "Unsuitable expression for Case floating." $
  caseFloatAppR <+ caseFloatCaseR <+ caseFloatLetR

-- | case scrut of wild t { _ -> body }
--    ==> let wild = scrut in body
-- May be followed by let-elimination.
-- Warning: does not capture GHC's intent to reduce scrut to WHNF.
caseWildR :: ReExpr
caseWildR = labeledR "reifyCaseWild" $
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

type FilterC a = TransformC a ()
type FilterE   = FilterC CoreExpr
type FilterTy  = FilterC Type

isTypeE :: FilterE
isTypeE = typeT successT

-- | Like tyConAppT, but for single type argument.
tyConApp1T :: (ExtendCrumb c, Monad m) =>
              Transform c m TyCon a -> Transform c m KindOrType b -> (a -> b -> z)
           -> Transform c m Type z
tyConApp1T ra rb h =
  do TyConApp _ [_] <- id
     tyConAppT ra (const rb) (\ a [b] -> h a b)

-- | Like 'buildDictionaryT' but uses 'lintExprT' to reject bogus dictionaries.
-- TODO: investigate and fix 'buildDictionaryT' instead.

buildDictionaryT' :: TransformC Type CoreExpr
buildDictionaryT' = setFailMsg "Couldn't build dictionary" $
                    tryR bashE . lintExprR . buildDictionaryT

{--------------------------------------------------------------------
    
--------------------------------------------------------------------}

-- Adapted from Andrew Farmer's code
-- <https://github.com/ku-fpg/hermit/issues/101#issuecomment-43463849>

data CustomC = CustomC { cDebugFlag :: Bool, cHermitC :: HermitC }

type TransformC a b = Transform CustomC HermitM a b
type RewriteC a = TransformC a a

onHermitC :: Unop HermitC -> Unop CustomC
onHermitC f c = c { cHermitC = f (cHermitC c) }

projectHermitC :: (HermitC -> a) -> (CustomC -> a)
projectHermitC r c = r (cHermitC c)

instance AddBindings CustomC where
  addHermitBindings bs = onHermitC (addHermitBindings bs)

instance BoundVars CustomC where
  boundVars = projectHermitC boundVars

instance ReadBindings CustomC where
  hermitDepth    = projectHermitC hermitDepth
  hermitBindings = projectHermitC hermitBindings

instance HasCoreRules CustomC where
    hermitCoreRules = projectHermitC hermitCoreRules

instance HasEmptyContext CustomC where
  setEmptyContext c =
    c { cDebugFlag = False
      , cHermitC = setEmptyContext (cHermitC c)
      }

instance ReadPath HermitC crumb => ReadPath CustomC crumb where
  absPath = projectHermitC absPath

--     Constraint is no smaller than the instance head
--       in the constraint: ReadPath HermitC crumb
--     (Use UndecidableInstances to permit this)

instance ExtendPath HermitC crumb => ExtendPath CustomC crumb where
  c @@ crumb = onHermitC (@@ crumb) c

data RewriteCCoreBox = RewriteCCoreBox (RewriteC Core) deriving Typeable

instance Extern (RewriteC Core) where
    type Box (RewriteC Core) = RewriteCCoreBox
    box = RewriteCCoreBox
    unbox (RewriteCCoreBox r) = r

debugR :: Bool -> RewriteC b -> RewriteH b
debugR b = liftContext (CustomC b)

-- TODO: Can I eliminate the CustomC requirement in debugR?

-- | Repeat a rewriter exactly @n@ times.
repeatN :: Monad m => Int -> Unop (Rewrite c m a)
repeatN n = serialise . replicate n

-- | Use in a stashed 'Def' to say that we don't want to dump.
bogusDefName :: String
bogusDefName = "$bogus-def-name$"

dropBogus :: Unop (Map Id CoreExpr)
dropBogus = Map.filterWithKey (\ v _ -> uqVarName v /= bogusDefName)

saveDefNoFloat :: String -> CoreExpr -> TransformM c a ()
saveDefNoFloat lab e = do v <- newIdT bogusDefName $* exprType e
                          constT (saveDef lab (Def v e))

-- | Dump the stash of definitions.
dumpStashR :: RewriteC CoreProg
dumpStashR = do stashed <- stashIdMapT
                already <- arr progBound
                let new = dropBogus (Map.difference stashed already)
                -- Drop these let bindings from program before extending.
                progRhsAnyR (anybuE (dropLets new))  -- or anytdR (repeat (dropLets new))
                  >>> arr (\ prog -> foldr add prog (Map.toList new))
 where
   add (v,rhs) = ProgCons (NonRec v rhs)

-- We only remove let bindings from the top-level of a definition.
-- They get floated there.
-- TODO: Drop unused stashed bindings.

dropStashedLetR :: ReExpr
dropStashedLetR = stashIdMapT >>= dropLets

-- Rewrite the right-hand sides of top-level definitions
progRhsAnyR :: ReExpr -> RewriteC CoreProg
progRhsAnyR r = progBindsAnyR (const (nonRecOrRecAllR id r))
 where
   nonRecOrRecAllR p q =
     recAllR (const (defAllR p q)) <+ nonRecAllR p q

-- (anybuE (dropLets new))

-- TODO: Handle recursive definition groups also.

-- reifyProg = progBindsT (const (tryR reifyDef >>> letFloatToProg)) concatProgs
-- progBindsAllR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => (Int -> Rewrite c m CoreBind) -> Rewrite c m CoreProg

-- NOTE: I'm converting the stash from a map over Label to a map over Id.
-- Look for a better way.

progBound :: CoreProg -> Map Id CoreExpr
progBound = foldMap bindNames . progToBinds
 where
   bindNames (NonRec v e) = Map.singleton v e
   bindNames (Rec bs)     = Map.fromList bs

stashIdMapT :: TransformM c a (Map Id CoreExpr)
stashIdMapT =
  (Map.fromList . Map.elems . fmap defToIdExpr) <$> constT getStash

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

-- | (,) ta' tb' (a `cast` coa) (b `cast` cob)  ==>
--   (,) ta tb a b `cast` coab
--  where `coa :: ta ~R ta'`, `cob :: tb ~R tb'`, and
--  `coab :: (ta,tb) ~R (ta',tb')`.
pairCastR :: ReExpr
pairCastR =
  do [_,_,Cast a coa,Cast b cob] <- snd <$> callNameT "GHC.Tuple.(,)"
     return $
       Cast (mkCoreTup [a,b])
            (mkTyConAppCo Representational pairTyCon [coa,cob])

-- TODO: Do I always want Representational here?
