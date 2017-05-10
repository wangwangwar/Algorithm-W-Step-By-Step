module Lib where

import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import qualified Text.PrettyPrint as PP

data Exp = EVar String
        | ELit Lit
        | EApp Exp Exp
        | EAbs String Exp
        | ELet String Exp Exp
        deriving (Eq, Ord)

data Lit = LInt Integer
        | LBool Bool
        deriving (Eq, Ord)

data Type = TVar String
        | TInt
        | TBool
        | TFun Type Type
        deriving (Eq, Ord)

data Scheme = Scheme [String] Type

class Types a where
    ftv :: a -> Set.Set String
    apply :: Subst -> a -> a

instance Types Type where
    ftv (TVar n) = Set.singleton n
    ftv TInt = Set.empty
    ftv TBool = Set.empty
    ftv (TFun t1 t2) = ftv t1 `Set.union` ftv t2

    apply s (TVar n) = case Map.lookup n s of
        Nothing -> TVar n
        Just t -> t
    apply s (TFun t1 t2) = TFun (apply s t1) (apply s t2)
    apply s t = t

instance Types Scheme where 
    ftv (Scheme vars t) = ftv t `Set.difference` Set.fromList vars
    apply s (Scheme vars t) = Scheme vars (apply (foldr Map.delete s vars) t)

instance Types a => Types [a] where
    apply s = map (apply s)
    ftv l = foldr (Set.union . ftv) Set.empty l

type Subst = Map.Map String Type

nullSubst :: Subst
nullSubst = Map.empty

-- map :: (a -> b) -> Map k a -> Map k b Source #
-- O(n). Map a function over all values in the map.
-- map (++ "x") (fromList [(5,"a"), (3,"b")]) == fromList [(3, "bx"), (5, "ax")]
composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = Map.map (apply s1) s2 `Map.union` s1

newtype TypeEnv = TypeEnv (Map.Map String Scheme)

-- 被称为 remove 的操作 Γ\x 移除 Γ 中有关 x 的绑定。
remove :: TypeEnv -> String -> TypeEnv
remove (TypeEnv env) var = TypeEnv (Map.delete var env)

instance Types TypeEnv where
    -- elems :: Map k a -> [a] Source #
    -- O(n). Return all elements of the map in the ascending order of their keys. Subject to list fusion.
    ftv (TypeEnv env) = ftv (Map.elems env)
    apply s (TypeEnv env) = TypeEnv (Map.map (apply s) env)

generalize :: TypeEnv -> Type -> Scheme
generalize env t = Scheme vars t
    where vars = Set.toList (ftv t `Set.difference` ftv env)


data TIEnv = TIEnv {}

data TIState = TIState { tiSupply :: Int }

type TI a = ExceptT String (ReaderT TIEnv (StateT TIState IO)) a

runTI :: TI a -> IO (Either String a, TIState)
runTI t = do 
    (res, st) <- runStateT (runReaderT (runExceptT t) initTIEnv) initTIState
    return (res, st)
    where 
        initTIEnv = TIEnv
        initTIState = TIState { tiSupply = 0 }

newTyVar :: String -> TI Type
newTyVar prefix = do 
    s <- get
    put s { tiSupply = tiSupply s + 1 }
    return (TVar (prefix ++ show (tiSupply s)))

instantiate :: Scheme -> TI Type
instantiate (Scheme vars t) = do
    nvars <- mapM (\_ -> newTyVar "a") vars
    let s = Map.fromList (zip vars nvars)
    return $ apply s t

-- 下面的是类型的 unification 方法。对于 t1 t2 两个类型，这个方法给出最通用（general）的合一（unifier）。
-- 合一是一个替换S，它使得 S(t1) ≡ S(t2)。 方法 varBind 将一个类型变量绑定为一个类型，并且返回这个绑定的替换，并且不会将一个变量绑定到自身。
mgu :: Type -> Type -> TI Subst
mgu (TFun l r) (TFun l' r') = do
    s1 <- mgu l l'
    s2 <- mgu (apply s1 r) (apply s1 r')
    return (s1 `composeSubst` s2)
mgu (TVar u) t = varBind u t
mgu t (TVar u) = varBind u t
mgu TBool TBool = return nullSubst
mgu t1 t2 = throwError $ "types do not unify: " ++ show t1 ++ " vs. " ++ show t2

varBind :: String -> Type -> TI Subst
varBind u t 
    | t == TVar u = return nullSubst
    | u `Set.member` ftv t = throwError $ "occurs check fails: " ++ u ++ " vs. " ++ show t
    | otherwise = return (Map.singleton u t)

tiLit :: Lit -> TI (Subst, Type)
tiLit (LInt _) = return (nullSubst, TInt)
tiLit (LBool _) = return (nullSubst, TBool)

ti :: TypeEnv -> Exp -> TI (Subst, Type)
ti (TypeEnv env) (EVar n) =
    case Map.lookup n env of 
        Nothing -> throwError $ "unbound variable: " ++ n
        Just sigma -> do t <- instantiate sigma
                         return (nullSubst, t)
ti _ (ELit l) = tiLit l
ti env (EAbs n e) = do
    tv <- newTyVar "a"
    let TypeEnv env' = remove env n
        env'' = TypeEnv (env' `Map.union` Map.singleton n (Scheme [] tv))
    (s1, t1) <- ti env'' e
    return (s1, TFun (apply s1 tv) t1)
ti env exp@(EApp e1 e2) = do
    tv <- newTyVar "a"
    (s1, t1) <- ti env e1
    (s2, t2) <- ti (apply s1 env) e2
    s3 <- mgu (apply s2 t1) (TFun t2 tv)
    return (s3 `composeSubst` s2 `composeSubst` s1, apply s3 tv)
    `catchError`
    \e -> throwError $ e ++ "\n in " ++ show exp
ti env (ELet x e1 e2) = do
    (s1, t1) <- ti env e1
    let TypeEnv env' = remove env x
        t' = generalize (apply s1 env) t1
        env'' = TypeEnv (Map.insert x t' env')
    (s2, t2) <- ti (apply s1 env'') e2
    return (s1 `composeSubst` s2, t2)

typeInference :: Map.Map String Scheme -> Exp -> TI Type
typeInference env e = do
    (s, t) <- ti (TypeEnv env) e
    return (apply s t)

test :: Exp -> IO ()
test e = do
    (res, _) <- runTI (typeInference Map.empty e)
    case res of
        Left err -> putStrLn $ show e ++ "\n " ++ err ++ "\n"
        Right t -> putStrLn $ show e ++ " :: " ++ show t ++ "\n"


instance Show Type where
    showsPrec _ x = shows (prType x)
prType             ::  Type -> PP.Doc
prType (TVar n)    =   PP.text n
prType TInt        =   PP.text "Int"
prType TBool       =   PP.text "Bool"
prType (TFun t s)  =   prParenType t PP.<+> PP.text "->" PP.<+> prType s
prParenType     ::  Type -> PP.Doc
prParenType  t  =   case t of
                      TFun _ _  -> PP.parens (prType t)
                      _         -> prType t

instance Show Exp where
    showsPrec _ x = shows (prExp x)
prExp                  ::  Exp -> PP.Doc
prExp (EVar name)      =   PP.text name
prExp (ELit lit)       =   prLit lit
prExp (ELet x b body)  =   PP.text "let" PP.<+> 
                           PP.text x PP.<+> PP.text "=" PP.<+>
                           prExp b PP.<+> PP.text "in" PP.$$
                           PP.nest 2 (prExp body)
prExp (EApp e1 e2)     =   prExp e1 PP.<+> prParenExp e2
prExp (EAbs n e)       =   PP.char '\\' PP.<> PP.text n PP.<+>
                           PP.text "->" PP.<+>
                           prExp e
                                                                   
prParenExp    ::  Exp -> PP.Doc
prParenExp t  =   case t of
                    ELet _ _ _  -> PP.parens (prExp t)
                    EApp _ _    -> PP.parens (prExp t)
                    EAbs _ _    -> PP.parens (prExp t)
                    _           -> prExp t

instance Show Lit where
    showsPrec _ x = shows (prLit x)
prLit            ::  Lit -> PP.Doc
prLit (LInt i)   =   PP.integer i
prLit (LBool b)  =   if b then PP.text "True" else PP.text "False"

instance Show Scheme where
    showsPrec _ x = shows (prScheme x)
prScheme                  ::  Scheme -> PP.Doc
prScheme (Scheme vars t)  =   PP.text "All" PP.<+>
                              PP.hcat 
                                (PP.punctuate PP.comma (map PP.text vars))
                              PP.<> PP.text "." PP.<+> prType t
