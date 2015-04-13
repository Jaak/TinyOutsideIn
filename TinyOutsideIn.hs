{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}

import Control.Applicative
import Control.Arrow (first)
import Control.Exception
import Control.Monad
import Control.Monad.IO.Class
import Data.IORef
import Data.List
import Data.Map (Map)
import Data.String
import Data.Typeable
import qualified Data.Map as Map

type Name = String

-- Levels are used to tell how deep in the implication tower was a meta
-- variable born. In deeper levels we may not unify meta variables that were
-- born in upper levels -- they are untouchable there. This is exactly the
-- "outside-in" approach, unifications can only happen from outside to in.
type Level = Int

type Unique = Int

{---------------------
 -- Syntax of types --
 ---------------------}

data TyVar
  = VarCon Name -- rigid type variable
  | VarMeta (IORef TyMeta) -- unifiable (or linked to some type)
  deriving (Eq, Typeable)

data TyMeta
  = MetaFlex Level Unique
  | MetaLink Type

instance IsString TyVar where
  fromString = VarCon

instance Show TyVar where
  show (VarCon x) = x
  show _ = "[]"

isMetaVar :: TyVar -> Bool
isMetaVar (VarMeta _) = True
isMetaVar _ = False

data Kind
  = KindType
  | KindSize
  deriving (Eq, Show, Typeable)

data TypeCon
  = TyConInt            -- t ::= int[s]
  | TyConBool           --    |  Bool
  | TyConFun            --    |  t1 -> t2
  | TyConList           --    |  [t]
  | TyConTuple          --    |  (t1, t2, ..., tn) 
  | TyConSizeLit Int    -- s ::= c  (size literal)
  | TyConAdd            --    |  s1 + s2
  | TyConMul            --    |  s1 * s2
  | TyConDiv            --    |  s1 / s2
  | TyConSub            --    |  s1 - s2
  | TyConWidth          --    |  width s
  deriving (Show, Eq, Typeable)

isSizeTyCon :: TypeCon -> Bool
isSizeTyCon t = case t of
  TyConSizeLit _ -> True
  TyConAdd -> True
  TyConMul -> True
  TyConDiv -> True
  TyConSub -> True
  TyConWidth -> True
  _ -> False
    
data TypePred
  = TruePred                       -- p ::= True
  | AndPred TypePred TypePred      --    |  p1 /\ p2
  | NotPred TypePred               --    |  ¬ p
  | HasFieldPred Type Int Type     --    |  t1.i : t2
  | EqPred Type Type               --    |  s1 = s2
  | LessPred Type Type             --    |  s1 < s2
  | LessEqualPred Type Type        --    |  s1 <= s2
  deriving (Eq, Typeable)

instance Show TypePred where
  show TruePred = "true"
  show (AndPred p1 p2) = show p1 ++ " ∧ " ++ show p2
  show (NotPred p) = "¬(" ++ show p ++ ")"
  show (HasFieldPred t1 i t2) = "HasField " ++ show t1 ++ " " ++ show i ++ " " ++ show t2
  show (EqPred t1 t2) = show t1 ++ " = " ++ show t2
  show (LessPred t1 t2) = show t1 ++ " < " ++ show t2
  show (LessEqualPred t1 t2) = show t1 ++ " <= " ++ show t2

andTypePreds :: [TypePred] -> TypePred
andTypePreds = foldr andTypePred TruePred

andTypePred :: TypePred -> TypePred -> TypePred
andTypePred TruePred b = b
andTypePred a TruePred = a
andTypePred a b = AndPred a b

data Type
  = TyVar Kind TyVar
  | TyApp TypeCon [Type]
  deriving (Eq, Typeable)

instance Num Type where
  fromInteger n = mkSizeLit (fromInteger n)
  (+) = mkAddType
  (*) = mkMulType
  abs = id
  signum = id
  negate = error "Can not negate"

instance Show Type where
  show (TyVar _ x) = show x
  show (TyApp con ts)
    | TyConInt <- con, [s] <- ts = "uint[" ++ show s ++ "]"
    | TyConBool <- con, [] <- ts = "bool"
    | TyConFun <- con, [t1, t2] <- ts = show t1 ++ " -> (" ++ show t2 ++ ")"
    | TyConList <- con, [t] <- ts = "[" ++ show t ++ "]"
    | TyConTuple <- con = "(" ++ concat (intersperse "," (map show ts)) ++  ")"
    | TyConSizeLit k <- con, [] <- ts = show k
    | TyConAdd <- con, [s1, s2] <- ts = "(" ++ show s1 ++ " + " ++ show s2 ++ ")" 
    | TyConMul <- con, [s1, s2] <- ts = "(" ++ show s1 ++ " * " ++ show s2 ++ ")"  
    | TyConDiv <- con, [s1, s2] <- ts = "(" ++ show s1 ++ " / " ++ show s2 ++ ")"  
    | TyConSub <- con, [s1, s2] <- ts = "(" ++ show s1 ++ " - " ++ show s2 ++ ")"  
    | TyConWidth <- con, [s] <- ts = "width " ++ show s
    | otherwise = "<ill formed type>"

mkIntType :: Type -> Type
mkIntType s = TyApp TyConInt [s]

mkTypeVarType :: Name -> Type
mkTypeVarType = TyVar KindType . VarCon

mkSizeVarType :: Name -> Type
mkSizeVarType = TyVar KindSize . VarCon

mkFunType :: Type -> Type -> Type
mkFunType t1 t2 = TyApp TyConFun [t1, t2]

mkListType :: Type -> Type
mkListType t = TyApp TyConList [t]

mkPairType :: Type -> Type -> Type
mkPairType t1 t2 = TyApp TyConTuple [t1, t2]

mkSizeLit :: Int -> Type
mkSizeLit s = TyApp (TyConSizeLit s) []

mkAddType :: Type -> Type -> Type
mkAddType t1 t2 = TyApp TyConAdd [t1, t2]

mkSubType :: Type -> Type -> Type
mkSubType t1 t2 = TyApp TyConSub [t1, t2]

mkMulType :: Type -> Type -> Type
mkMulType t1 t2 = TyApp TyConMul [t1, t2]

mkDivType :: Type -> Type -> Type
mkDivType t1 t2 = TyApp TyConDiv [t1, t2]

mkWidthType :: Type -> Type
mkWidthType t1 = TyApp TyConWidth [t1]

{-------------------
 -- Kind checking --
 -------------------}

-- | Kind checking. Also verify that the type is well formed.
kindCheck :: Kind -> Type -> Bool
kindCheck k (TyVar k' _) = k == k'
kindCheck KindType (TyApp con ts) 
  | TyConInt <- con, [s] <- ts = isSizeType s
  | TyConBool <- con, [] <- ts = True
  | TyConFun <- con, [t1, t2] <- ts = kindCheck KindType t1 && kindCheck KindType t2
  | TyConList <- con, [t] <- ts = kindCheck KindType t
  | TyConTuple <- con = and $ map (kindCheck KindType) ts
kindCheck KindSize (TyApp con ss)
  | TyConSizeLit _ <- con, [] <- ss = True
  | TyConAdd <- con, [s1, s2] <- ss = all isSizeType ss
  | TyConMul <- con, [s1, s2] <- ss = all isSizeType ss 
  | TyConDiv <- con, [s1, s2] <- ss = all isSizeType ss 
  | TyConSub <- con, [s1, s2] <- ss = all isSizeType ss 
  | TyConWidth <- con, [s] <- ss = isSizeType s
kindCheck _ _ = False

-- | Check is given type is a size type.
-- Expects kind checked type!
isSizeType :: Type -> Bool
isSizeType (TyVar KindSize) = True
isSizeType (TyApp con _) = isSizeTyCon con
isSizeType _ = False

-- Note that we only allow equality predicate between size types in user
-- written code and not equality between regular types.  This is just a
-- simplification, nothing fundamental stops us from supporting general type
-- equality. During unification predicates between regular types may also be
-- emitted.
kindCheckPred :: TypePred -> Bool
kindCheckPred TruePred = True
kindCheckPred (AndPred p1 p2) = kindCheckPred p1 && kindCheckPred p2
kindCheckPred (NotPred p) = kindCheckPred p
kindCheckPred (HasFieldPred t1 _ t2) = kindCheck KindType t1 && kindCheck KindType t2
kindCheckPred (EqPred t1 t2) = isSizeType t1 && isSizeType t2
kindCheckPred (LessPred t1 t2) = isSizeType t1 && isSizeType t2
kindCheckPred (LessEqualPred t1 t2) = isSizeType t1 && isSizeType t2

data TypeScheme
  = TypeForall [Name] TypePred Type -- \forall a1 a2 ... an. p => t

{-----------------
 -- Constraints --
 -----------------}

data Constr
  = ConstrEmpty                -- c ::= \varepsilon
  | ConstrWanted TypePred      --    |  p
  | ConstrAnd Constr Constr    --    |  c1, c2
  | ConstrImpl TypePred Constr --    |  p -> c
  deriving (Eq)

instance Show Constr where
  show ConstrEmpty = "ɛ"
  show (ConstrWanted p) = show p
  show (ConstrAnd c1 c2) = show c1 ++ "\n" ++ show c2
  show (ConstrImpl p c) = show p ++ " ->\n" ++ unlines (map indent (lines (show c)))
    where indent = ("  " ++)

constrAnd :: Constr -> Constr -> Constr
constrAnd c1 ConstrEmpty = c1
constrAnd ConstrEmpty c2 = c2
constrAnd c1 c2 = ConstrAnd c1 c2

addWanted :: TypePred -> Constr -> Constr
addWanted TruePred constr = constr
addWanted tyPred ConstrEmpty = ConstrWanted tyPred
addWanted tyPred constr = ConstrAnd constr (ConstrWanted tyPred)

{------------------
 -- Type unifier --
 ------------------}

-- this is not meant to be pretty
data TypeError
  = ErrOccursCheck
  | ErrUnifFail Type Type
  | ErrKindMismatch Type Type
  | ErrVarKindMismatch Kind Name
  | ErrInvalidIfCondKind TypePred
  | ErrNotSizeType Type
  | ErrFreeVariableInTypeScheme Name
  | ErrFreeVariable Name
  | ErrICE -- internal compile error
  deriving (Show, Typeable)

instance Exception TypeError

-- | Type unification. Returns true if any meta variables have been unified.
-- The first parameter is the expected type and the second one is what we are
-- checking against. The type errors should be in the form "expected ty1, got
-- ty2". Some care has been taken to make sure that those errors are in correct
-- order.
unifyTypes :: Type -> Type -> TcM Bool
unifyTypes ty1 ty2 = go ty1 ty2
  where
    go (TyVar k x) (TyVar k' x')
      | k /= k' = tcThrow (ErrKindMismatch ty1 ty2)
      | x == x' = return True
    go (TyVar k (VarMeta x)) t2 = unifyMetaTyVar False k x t2
    go t1 (TyVar k (VarMeta y)) = unifyMetaTyVar True k y t1
    go t1 t2 | isSizeType t1, isSizeType t2 = delayUnif False t1 t2 >> return False
    go (TyApp c ts) (TyApp c' ts')
      | c == c', length ts == length ts' = or <$> zipWithM go ts ts'
    go t1 t2 = tcThrow (ErrUnifFail t1 t2)

-- | Try to unify a meta variable "u" with type "t". Performs occurs check if needed.
-- Size and type variables are handled differently by unification. Type
-- variables can not be solved if occurs check fails and as we do not have
-- dependent (only size dependent!) types we don't have to bother with
-- tracking untouchable variables.
unifyMetaTyVar :: Bool -> Kind -> IORef TyMeta -> Type -> TcM Bool
unifyMetaTyVar swapped k u t = do
  uInfo <- tcReadRef u
  occ <- occursIn u t
  when (occ && k == KindType) $
    tcThrow ErrOccursCheck
  case uInfo of
    MetaLink t' -> if swapped
      then unifyTypes t' t
      else unifyTypes t t'
    MetaFlex metaVarLevel _ -> do
      untouchable <- tcIsUntouchable metaVarLevel
      if occ || untouchable
        then delayUnif swapped (TyVar k (VarMeta u)) t >> return False
        else tcWriteRef u (MetaLink t) >> return True

-- | Delay unification between to types until later solving.
-- Equality of size types is definitely always delayed but also unification of
-- untouchable variable is delayed.
delayUnif :: Bool -> Type -> Type -> TcM ()
delayUnif True  t1 t2 = tcAddWanted (EqPred t2 t1)
delayUnif False t1 t2 = tcAddWanted (EqPred t1 t2)

tcFreshMetaTyVar :: TcM TyVar
tcFreshMetaTyVar = do
  flex <- MetaFlex <$> tcGetLevel <*> tcNextUnique
  VarMeta <$> tcNewRef flex

-- | Occurs check.
occursIn :: IORef TyMeta -> Type -> TcM Bool
occursIn u = go
  where
    
    go (TyVar _ (VarCon _)) = return False
    go (TyVar _ (VarMeta v))
      | u == v = return True
      | otherwise = do
        vInfo <- tcReadRef v
        case vInfo of
          MetaLink t -> go t
          MetaFlex _ _ -> return False
    go (TyApp con ts) = or <$> mapM go ts

-- | Constraint simplification. It is not meant to solve all of the
-- existentials. The resulting constaints are the ones that could not be
-- solved.
simplifyConstr :: Constr -> TcM Constr
simplifyConstr origConstr = do
  continueRef <- tcNewRef False
  let
    goC ConstrEmpty = pure ConstrEmpty
    goC (ConstrWanted p) = goP p
    goC (ConstrAnd c1 c2) = constrAnd <$> goC c1 <*> goC c2
    goC (ConstrImpl p c) = ConstrImpl p <$> tcWithNextLevel (goC c)

    goP (EqPred t1 t2) =
      tcCollectWanted $ do
        b <- unifyTypes t1 t2
        when b $
          tcWriteRef continueRef True
    goP (AndPred p1 p2) = constrAnd <$> goP p1 <*> goP p2
    goP p = pure (ConstrWanted p)
  
    loop c = do
      tcWriteRef continueRef False
      c' <- goC c
      b <- tcReadRef continueRef
      if b
        then loop c'
        else return c
  loop origConstr

-- Replace flex type variable with something printable only used for a bit
-- prettier printig. unifiable variables are denoted with "t". The name also
-- mentions the type variable name.
replaceFlex :: Constr -> TcM Constr
replaceFlex = goC
  where

    goC ConstrEmpty = pure ConstrEmpty
    goC (ConstrWanted p) = ConstrWanted <$> goP p
    goC (ConstrAnd c1 c2) = constrAnd <$> goC c1 <*> goC c2
    goC (ConstrImpl p c) = ConstrImpl <$> goP p <*> goC c

    goP TruePred = return TruePred
    goP (AndPred p1 p2) = AndPred <$> goP p1 <*> goP p2
    goP (NotPred p1) = NotPred <$> goP p1
    goP (HasFieldPred t1 i t2) = HasFieldPred <$> goT t1 <*> pure i <*> goT t2
    goP (EqPred t1 t2) = EqPred <$> goT t1 <*> goT t2
    goP (LessPred t1 t2) = LessPred <$> goT t1 <*> goT t2
    goP (LessEqualPred t1 t2) = LessEqualPred <$> goT t1 <*> goT t2

    goT t@(TyVar k (VarMeta r)) = do
      vInfo <- tcReadRef r
      case vInfo of
        MetaFlex l u -> pure $ TyVar k (VarCon ("t" ++ show u ++ "{" ++ show l ++ "}"))
        MetaLink t' -> goT t'
    goT t@(TyVar _ x) = return t
    goT (TyApp con ts) = TyApp con <$> mapM goT ts


{---------------------
 -- Simple language --
 ---------------------}

data Expr
  = ExprVar Name                         -- e ::= x
  | ExprLam Name Expr                    --    |  \x -> e
  | ExprApp Expr Expr                    --    |  e1 e2
  | ExprLet Name (Maybe Type) Expr Expr  --    |  let x = e1 in e2
  | ExprSelect Expr Int                  --    |  e.i
  | ExprTypeIf TypePred Expr Expr        --    |  if p then e1 else e2
  | ExprSlice Expr Type Type             --    |  e[s1 : s2]

instance IsString Expr where
  fromString = ExprVar

{------------------
 -- Type checker --
 ------------------}

tcFreshVar :: Kind -> TcM Type
tcFreshVar k = TyVar k <$> tcFreshMetaTyVar

tcFreshTypeVar :: TcM Type
tcFreshTypeVar = tcFreshVar KindType

-- | Instantiate \forall bound variables in type scheme with fresh meta
-- variables.
-- TODO: for all size variables "n" in the type we need constaint "0 <= n".
tcInstantiateScheme :: TypeScheme -> TcM (TypePred, Type)
tcInstantiateScheme (TypeForall xs forallPred forallBody) = do
  envRef <- tcNewRef Map.empty
  let

    subTy :: Type -> TcM Type
    subTy (TyVar _ (VarCon x))
      | notElem x xs = tcThrow (ErrFreeVariableInTypeScheme x)
    subTy (TyVar k (VarCon x)) = do
      env <- tcReadRef envRef
      case Map.lookup x env of
        Nothing -> do
          v <- tcFreshVar k
          tcWriteRef envRef (Map.insert x v env)
          return v
        Just v -> do
          if not (kindCheck k v)
            then tcThrow (ErrVarKindMismatch k x)
            else return v
    subTy (TyApp con ts) = TyApp con <$> mapM subTy ts

    subPred :: TypePred -> TcM TypePred
    subPred TruePred = pure TruePred
    subPred (NotPred p1) = NotPred <$> subPred p1
    subPred (AndPred p1 p2) = AndPred <$> subPred p1 <*> subPred p2
    subPred (HasFieldPred t1 i t2) = HasFieldPred <$> subTy t1 <*> pure i <*> subTy t2
    subPred (EqPred t1 t2) = EqPred <$> subTy t1 <*> subTy t2
    subPred (LessPred t1 t2) = LessPred <$> subTy t1 <*> subTy t2
    subPred (LessEqualPred t1 t2) = LessEqualPred <$> subTy t1 <*> subTy t2

  (,) <$> subPred forallPred <*> subTy forallBody

-- | Check that "width" is computed of non-negative integers and
-- devision-by-zero is impossible. For sake of simplicity we just check that
-- the divisor is a positive integer.
tcCheckType :: Type -> TcM ()
tcCheckType (TyVar _ _) = return ()
tcCheckType (TyApp con ts) = do
  case con of
    TyConWidth | [s] <- ts -> tcAddWanted (LessEqualPred 0 s)
    TyConDiv | [_, s2] <- ts -> tcAddWanted (LessPred 0 s2)
    _ -> return ()
  mapM_ tcCheckType ts

-- | Check that types inside a predicate are good (see tcCheckType).
tcCheckTypePred :: TypePred -> TcM ()
tcCheckTypePred TruePred = return ()
tcCheckTypePred (NotPred p1) = tcCheckTypePred p1
tcCheckTypePred (AndPred p1 p2) = tcCheckTypePred p1 >> tcCheckTypePred p2
tcCheckTypePred (HasFieldPred t1 i t2) = tcCheckType t1 >> tcCheckType t2
tcCheckTypePred (EqPred t1 t2) = tcCheckType t1 >> tcCheckType t2
tcCheckTypePred (LessPred t1 t2) = tcCheckType t1 >> tcCheckType t2
tcCheckTypePred (LessEqualPred t1 t2) = tcCheckType t1 >> tcCheckType t2

-- | Expression type inference.
tcInferExpr :: Expr -> TcM Type
tcInferExpr e = do
  t <- tcFreshTypeVar
  tcExpr t e
  return t

-- | Expression type checking.
tcExpr :: Type -> Expr -> TcM ()
tcExpr resTy (ExprVar x) = do
  schemeTy <- tcLookupScheme x
  case schemeTy of
    Nothing -> do
      varTy <- tcFindVarTy x
      void (unifyTypes resTy varTy)
    Just ty -> do
      (pred, ty') <- tcInstantiateScheme ty
      tcAddWanted pred
      void (unifyTypes ty' resTy)
tcExpr resTy (ExprLam x e) = do
  argTy <- tcFreshTypeVar
  retTy <- tcFreshTypeVar
  unifyTypes resTy (argTy `mkFunType` retTy)
  tcSetVarTy x argTy $
    tcExpr retTy e
tcExpr resTy (ExprApp e1 e2) = do
  e1Ty <- tcInferExpr e1
  e2Ty <- tcInferExpr e2
  void (unifyTypes (e2Ty `mkFunType` resTy) e1Ty)
tcExpr resTy (ExprLet x Nothing e1 e2) = do
  t <- tcInferExpr e1
  tcSetVarTy x t $
    tcExpr resTy e2
tcExpr resTy (ExprLet x (Just t) e1 e2) = do
  tcExpr t e1
  tcSetVarTy x t $
    tcExpr resTy e2
tcExpr resTy (ExprSelect e i) = do
  structTy <- tcInferExpr e
  tcAddWanted (HasFieldPred structTy i resTy)
tcExpr resTy (ExprTypeIf pred e1 e2)
  | not (kindCheckPred pred) = tcThrow (ErrInvalidIfCondKind pred)
  | otherwise = do
    tcCheckTypePred pred
    tcWithNextLevel $ do
      c1 <- tcCollectWanted (tcExpr resTy e1)
      c2 <- tcCollectWanted (tcExpr resTy e2)
      tcAddImpl pred c1
      tcAddImpl (NotPred pred) c2
tcExpr resTy (ExprSlice e s1 s2)
  | not (isSizeType s1) = tcThrow (ErrNotSizeType s1)
  | not (isSizeType s2) = tcThrow (ErrNotSizeType s2)
  | otherwise = do
    tcCheckType s1
    tcCheckType s2
    n <- tcFreshVar KindSize
    tcExpr (mkIntType n) e
    unifyTypes resTy (mkIntType (mkSubType s2 s1))
    -- 0 <= s1 <= s2 <= n
    tcAddWanted (LessEqualPred 0 s1)
    tcAddWanted (LessEqualPred s1 s2)
    tcAddWanted (LessEqualPred s2 n)

{------------------
 -- Example code --
 ------------------}

a, b, c, d :: Type
a = mkTypeVarType "a"
b = mkTypeVarType "b"
c = mkTypeVarType "c"
d = mkTypeVarType "d"

i, n, m, k :: Type
i = mkSizeVarType "i"
n = mkSizeVarType "n"
m = mkSizeVarType "m"
k = mkSizeVarType "k"

infixl 0 $$
($$) :: Expr -> Expr -> Expr
x $$ y = ExprApp x y

infix 4 ~~
(~~) :: Type -> Type -> TypePred
(~~) = EqPred

addE :: Expr -> Expr -> Expr
addE e1 e2 = "add" $$ e1 $$ e2

catE :: Expr -> Expr -> Expr
catE e1 e2 = "cat" $$ e1 $$ e2

letT :: Name -> Type -> Expr -> Expr -> Expr
letT x t e1 e2 = ExprLet x (Just t) e1 e2

ifE :: TypePred -> Expr -> Expr -> Expr
ifE = ExprTypeIf

letE :: Name -> Expr -> Expr -> Expr
letE x e1 e2 = ExprLet x Nothing e1 e2

exFoo :: (Expr, Type)
exFoo = (e, t)
  where
    t = mkIntType n `mkFunType` mkIntType n
    e = ExprLam "x" ("x" `addE` ifE (n ~~ 0) "zero" ("x" `addE` "one"))

-- map (\x -> x.0)
exFsts :: (Expr, Type)
exFsts = (e, t)
  where
    t = mkListType (mkPairType a b) `mkFunType` mkListType a
    e = "map" $$ ExprLam "x" (ExprSelect "x" 0)

-- PrefixOR, but uses sum (instead of OR) as what really matters are types.
exPrefixOR :: (Expr, Type)
exPrefixOR = (e, t)
  where
    t = mkIntType n `mkFunType` mkIntType n
    nHalf = mkDivType n 2
    e = ExprLam "p" $
      ifE (n ~~ 0) "p" $
        ifE (n ~~ 1) "p" $
          letE "x" ("prefixOR" $$ ExprSlice "p" 0 nHalf) $
          letE "y" ("prefixOR" $$ ExprSlice "p" nHalf n) $
          letE "b" ("zext" $$ ExprSlice "y" 0 1) $
          letE "r" (addE "x" "b") $
          catE "r" "y"

-- used to be a bug
exTest1 :: (Expr, Type)
exTest1 = (e, t)
  where
    e = letE "t" (ifE (n ~~ 0) "zero" "one") "t"
    t = mkIntType n

exTest2 :: (Expr, Type)
exTest2 = (e, t)
  where
    e = letE "x" ("zext" $$ "zero") $ ifE (n ~~ 0) "x" "x"
    t = mkIntType n

-- run "printWanted exFoo" for instance
printWanted :: (Expr, Type) -> IO ()
printWanted (e, t) = runTcM $ do
  tcExpr t e
  wanted <- replaceFlex =<< simplifyConstr =<< tcGetWanted
  liftIO $ putStrLn "System to solve:"
  tcPrint wanted

initialTypeEnv :: [(Name, TypeScheme)]
initialTypeEnv =
  [ ("add", TypeForall ["n"] TruePred (mkIntType n `mkFunType` (mkIntType n `mkFunType` mkIntType n)))
  , ("map", TypeForall ["a", "b"] TruePred ((a `mkFunType` b) `mkFunType` (mkListType a `mkFunType` mkListType b)))
  , ("zero", TypeForall [] TruePred (mkIntType (mkSizeLit 0)))
  , ("one", TypeForall ["n"] (LessPred (mkSizeLit 0) n) (mkIntType n))
  , ("zext", TypeForall ["n", "m"] (LessEqualPred n m) (mkIntType n `mkFunType` mkIntType m))
  , ("trunc", TypeForall ["n", "m"] (LessEqualPred m n) (mkIntType n `mkFunType` mkIntType m))
  , ("prefixOR", TypeForall ["n"] TruePred (mkIntType n `mkFunType` mkIntType n))
  , ("cat", TypeForall ["n", "m"] TruePred (mkIntType n `mkFunType` (mkIntType m `mkFunType` mkIntType (mkAddType n m))))
  ]

{--------------------------------
 -- Simple type checking monad --
 --------------------------------}

data TcEnv = TcEnv {
    _tyLevel :: Int,
    _tyEnv :: Map Name Type,
    _tyPoly :: Map Name TypeScheme,
    _unique :: IORef Unique,
    _wanted :: IORef Constr
  }

mkEmptyTcEnv :: IO TcEnv
mkEmptyTcEnv = do
  wantedRef <- newIORef ConstrEmpty
  uniqueRef <- newIORef 0
  return $ TcEnv {
    _tyLevel = 0,
    _wanted = wantedRef,
    _tyEnv = Map.empty,
    _unique = uniqueRef,
    _tyPoly = Map.fromList initialTypeEnv
  }

newtype TcM a = TcM {
    unTcM :: TcEnv -> IO a
  }

runTcM :: TcM a -> IO a
runTcM m = do
  emptyTcEnv <- mkEmptyTcEnv
  unTcM m emptyTcEnv

instance Functor TcM where
  fmap f m = TcM $ \env -> f `fmap` unTcM m env

instance Applicative TcM where
  pure x = TcM $ \_ -> pure x
  mf <*> mx = TcM $ \env -> unTcM mf env <*> unTcM mx env

instance Monad TcM where
  return = pure
  mx >>= f = TcM $ \env -> unTcM mx env >>= \x -> unTcM (f x) env

instance MonadIO TcM where
  liftIO act = TcM $ \_ -> act

tcPrint :: Show a => a -> TcM ()
tcPrint = liftIO . print

tcNewRef :: a -> TcM (IORef a)
tcNewRef = liftIO . newIORef
  
tcModifyRef :: IORef a -> (a -> a) -> TcM ()
tcModifyRef ioref f = liftIO (modifyIORef ioref f)

tcReadRef :: IORef a -> TcM a
tcReadRef = liftIO . readIORef

tcWriteRef :: IORef a -> a -> TcM ()
tcWriteRef r x = liftIO $ writeIORef r x

tcThrow :: Exception e => e -> TcM a
tcThrow = liftIO . throwIO

tcEnv :: TcM TcEnv
tcEnv = TcM return

tcWithEnv :: (TcEnv -> TcEnv) -> TcM a -> TcM a
tcWithEnv f tc = TcM $ \env -> unTcM tc (f env)

tcSetVarTy :: Name -> Type -> TcM a -> TcM a
tcSetVarTy x t = tcWithEnv $ \env -> env { _tyEnv = Map.insert x t (_tyEnv env) }

tcGetLevel :: TcM Level
tcGetLevel = _tyLevel <$> tcEnv

tcWithLevel :: Level -> TcM a -> TcM a
tcWithLevel l = tcWithEnv (\env -> env { _tyLevel = l })

tcWithNextLevel :: TcM a -> TcM a
tcWithNextLevel = tcWithEnv (\env -> env { _tyLevel = _tyLevel env + 1 })

tcLookupScheme :: Name -> TcM (Maybe TypeScheme)
tcLookupScheme x = Map.lookup x . _tyPoly <$> tcEnv

tcFindVarTy :: Name -> TcM Type
tcFindVarTy x = do
  env <- _tyEnv <$> tcEnv
  case x `Map.lookup` env of
    Nothing -> tcThrow (ErrFreeVariable x)
    Just ty -> return ty

tcGetWanted :: TcM Constr
tcGetWanted = do
  wantedRef <- _wanted <$> tcEnv
  tcReadRef wantedRef

tcAddImpl :: TypePred -> Constr -> TcM ()
tcAddImpl pred constr = do
  wantedRef <- _wanted <$> tcEnv
  tcModifyRef wantedRef (constrAnd (ConstrImpl pred constr))

tcAddWanted :: TypePred -> TcM ()
tcAddWanted pred = do
  wantedRef <- _wanted <$> tcEnv
  tcModifyRef wantedRef (addWanted pred)

tcCollectWanted :: TcM () -> TcM Constr
tcCollectWanted act = do
  newWantedRef <- tcNewRef ConstrEmpty
  tcWithEnv (\env -> env { _wanted = newWantedRef }) act
  tcReadRef newWantedRef

tcNextUnique :: TcM Unique
tcNextUnique = do
  uniqueRef <- _unique <$> tcEnv
  u <- tcReadRef uniqueRef
  tcWriteRef uniqueRef (u + 1)
  return u

tcIsUntouchable :: Level -> TcM Bool
tcIsUntouchable vl = (<) <$> pure vl <*> tcGetLevel
