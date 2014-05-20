{-# LANGUAGE CPP, Rank2Types, ConstraintKinds, PatternGuards, ViewPatterns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-} -- see below
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
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
  , isType, exprType', pairTy
  , tcFind0, tcFind, tcFind2
  , tcApp0, tcApp1, tcApp2
  , isPairTC, isPairTy, isEitherTy, isUnitTy, isBoolTy
  , unliftedType
  , apps, apps', callSplitT, callNameSplitT, unCall, unCall1
  , collectForalls, subst, isTyLam, setNominalRole_maybe
  , isVarT, isLitT
    -- * HERMIT utilities
  , liftedKind, unliftedKind
  , ReExpr, ReCore, FilterH, FilterE, OkCM, TransformU, findTyConT, isTypeE
  , mkUnit, mkPair, mkLeft, mkRight, mkEither
  , InCoreTC
  , Observing, observeR', tries, triesL, labeled
  , varLitE, uqVarName, typeEtaLong, simplifyE
  , anytdE, anybuE, inAppTys , isAppTy
  , letFloatToProg
  , concatProgs
  , rejectR , rejectTypeR
  , simplifyExprT, whenChangedR
  , showPprT
  , externC
  , unJustT, tcViewT, unFunCo
  , lamFloatCastR, castCastR
  , bashExtendedWithE
  , CustomC(..),liftToHermitC, projectHermitC, debugR -- , liftCustomC
  ) where

import Prelude hiding (id,(.))

import Control.Category (Category(..),(>>>))
import Data.Functor ((<$>))
import Control.Applicative (Applicative(..))
import Control.Arrow (Arrow(..))
import Data.List (intercalate)
import Text.Printf (printf)
import Control.Monad.IO.Class (MonadIO)

-- GHC
import Unique(hasKey)
import PrelNames (
  liftedTypeKindTyConKey,unliftedTypeKindTyConKey,constraintKindTyConKey,
  eitherTyConName)
import SimplCore (simplifyExpr)

-- import Language.KURE.Transform (apply)
import HERMIT.Core (CoreProg(..),bindsToProg,progToBinds,exprAlphaEq)
import HERMIT.Monad (HermitM,HasModGuts(..),HasHscEnv(..),newIdH)
import HERMIT.Context (BoundVars(..),AddBindings(..),ReadBindings(..),HermitC)
-- Note that HERMIT.Dictionary re-exports HERMIT.Dictionary.*
import HERMIT.Dictionary
  ( findIdT, callT, callNameT, simplifyR, letFloatTopR
  , observeR, bracketR, bashExtendedWithR
#ifdef WatchFailures
  , traceR
#endif
  )
-- import HERMIT.Dictionary (traceR)
import HERMIT.GHC hiding (FastString(..))
import HERMIT.Kure hiding (apply)
import HERMIT.External (External,external,ExternalName)

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

isVarT :: TransformH CoreExpr ()
isVarT = varT successT

isLitT :: TransformH CoreExpr ()
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

-- Common context & monad constraints
-- type OkCM c m =
--   ( HasDynFlags m, Functor m, MonadThings m, MonadCatch m
--   , BoundVars c, HasModGuts m )

type OkCM c m = 
  ( BoundVars c, Functor m, HasDynFlags m, HasModGuts m, HasHscEnv m
  , MonadCatch m, MonadIO m, MonadThings m )

type TransformU b = forall c m a. OkCM c m => Transform c m a b

-- Apply a named id to type and value arguments.
apps' :: String -> [Type] -> [CoreExpr] -> TransformU CoreExpr
apps' s ts es = (\ i -> apps i ts es) <$> findIdT s

type ReExpr = RewriteH CoreExpr
type ReCore = RewriteH Core

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
unCall :: String -> TransformH CoreExpr [CoreExpr]
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

observeR' :: Observing -> InCoreTC t => String -> RewriteH t
observeR' True  = observeR
observeR' False = const idR

tries :: InCoreTC t => [RewriteH t] -> RewriteH t
tries = foldr (<+) ({- observeR' "Unhandled" >>> -} fail "unhandled")

triesL :: InCoreTC t => Observing -> [(String,RewriteH t)] -> RewriteH t
triesL observing = tries . map (labeled observing)

-- labeled :: InCoreTC t => Observing -> (String, TransformH a t) -> TransformH a t
-- labeled observing (label,trans) = trans >>> observeR' observing label

#ifdef WatchFailures
scopeR :: InCoreTC a => String -> Unop (RewriteH a)
scopeR label r = traceR ("Try " ++ label ) >>>
                 -- r
                 (r <+ (traceR (label ++ " failed") >>> fail "scopeR"))
#endif

labeled :: InCoreTC a => Observing -> (String, RewriteH a) -> RewriteH a
labeled observing (label,r) =
#ifdef WatchFailures
  scopeR label $
#endif
  (if observing then bracketR label else id) r

-- mkVarName :: MonadThings m => Transform c m Var (CoreExpr,Type)
-- mkVarName = contextfreeT (mkStringExpr . uqName . varName) &&& arr varType

varLitE :: Var -> CoreExpr
varLitE = Lit . mkMachString . uqVarName

uqVarName :: Var -> String
uqVarName = uqName . varName

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

letFloatToProg :: TransformH CoreBind CoreProg
letFloatToProg = arr (flip ProgCons ProgNil) >>> tryR letFloatTopR

concatProgs :: [CoreProg] -> CoreProg
concatProgs = bindsToProg . concatMap progToBinds

-- | Reject if condition holds. Opposite of 'acceptR'
rejectR :: Monad m => (a -> Bool) -> Rewrite c m a
rejectR f = acceptR (not . f)

-- | Reject if condition holds on an expression's type.
rejectTypeR :: Monad m => (Type -> Bool) -> Rewrite c m CoreExpr
rejectTypeR f = rejectR (f . exprType)

simplifyExprT :: ReExpr
simplifyExprT =
  whenChangedR "simplify-expr" $
    prefixFailMsg "simplify-expr failed: " $
      contextfreeT $ \ e ->
        do dflags <- getDynFlags
           liftIO $ simplifyExpr dflags e

-- | Succeed only if the given rewrite actually changes the 
whenChangedR :: String -> RewriteH CoreExpr -> RewriteH CoreExpr
whenChangedR name r =
  do (e,e') <- (r &&& idR)
     guardMsg (not (exprAlphaEq e e'))
      (name ++ ": result is unchanged from input.")
     return e'

-- | Get a GHC pretty-printing
showPprT :: (HasDynFlags m, Outputable x, Monad m) =>
            x -> Transform c m a String
showPprT x = do dynFlags <- constT getDynFlags
                return (showPpr dynFlags x)

externC :: Injection a Core =>
           ExternalName -> RewriteH a -> String -> External
externC name rew help = external name (promoteR rew :: ReCore) [help]

-- | unJust as transform. Fails on Nothing.
-- Already in Kure?
unJustT :: Monad m => Transform c m (Maybe a) a
unJustT = do Just x <- idR
             return x

-- | GHC's tcView as a rewrite
tcViewT :: RewriteH Type
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

-- | Like bashExtendedWith, but for expressions
bashExtendedWithE :: [ReExpr] -> ReExpr
bashExtendedWithE rs = extractR (bashExtendedWithR (promoteR <$> rs))

type FilterH a = TransformH a ()
type FilterE = FilterH CoreExpr

isTypeE :: FilterE
isTypeE = typeT successT

{--------------------------------------------------------------------
    
--------------------------------------------------------------------}

-- Adapted from Andrew Farmer's code
-- <https://github.com/ku-fpg/hermit/issues/101#issuecomment-43463849>

data CustomC = CustomC { cDebugFlag :: Bool, cHermitC :: HermitC }

liftToHermitC :: Unop HermitC -> Unop CustomC
liftToHermitC f c = c { cHermitC = f (cHermitC c) }

projectHermitC :: (HermitC -> a) -> (CustomC -> a)
projectHermitC r c = r (cHermitC c)

instance AddBindings CustomC where
  addHermitBindings bs = liftToHermitC (addHermitBindings bs)

instance BoundVars CustomC where
  boundVars = projectHermitC boundVars

instance ReadBindings CustomC where
  hermitDepth    = projectHermitC hermitDepth
  hermitBindings = projectHermitC hermitBindings

instance ReadPath HermitC crumb => ReadPath CustomC crumb where
  -- | Read the current absolute path.
  absPath = projectHermitC absPath

--     Constraint is no smaller than the instance head
--       in the constraint: ReadPath HermitC crumb
--     (Use UndecidableInstances to permit this)

-- Then you can write something like:

debugCustomR :: Injection a CoreTC => Unop (Rewrite CustomC HermitM a)
debugCustomR rr = do
    c <- contextT
    if cDebugFlag c then bracketR "debug" rr else rr

debugR :: Injection b CoreTC =>
          Rewrite CustomC HermitM b -> RewriteH b
debugR r = liftContext (CustomC True) (debugCustomR r)

-- TODO: Can I eliminate the CustomC requirement in debugR?

-- And call it from your plugin with:

-- run $ liftCustomC True $ focusR (occurenceOfT "fib") (debugR inlineR)

