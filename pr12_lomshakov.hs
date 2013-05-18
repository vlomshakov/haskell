import Data.List
import Data.Maybe
import Data.Char
import Control.Monad.State

-- test
-- two = \fx.f(f x), three  (a->a)->a->a
-- pow \m n -> n m
-- (pow :@ two) :@ three
-- \ f g -> g (\y . g f)
-- \ x.x x - error


--------------------
-- Representation of Terms
type Sym = String
data Expr
        = Var Sym
        | Expr :@ Expr
        | Lam Sym Expr
        deriving (Eq, Read, Show)


---------------------
-- Finds free variables
freeVars (Var v)     = [v]
freeVars (t1 :@ t2) = freeVars t1 `union` freeVars t2
freeVars (Lam v t)   = freeVars t \\ [v]

----------------------
-- Representation of Types
data Type
    = TVar Sym
    | Type :-> Type
    deriving (Eq, Read, Show)
infixr 5 :->



occurCheck t (v1 :-> v2) = occurCheck t v1 || occurCheck t v2
occurCheck t  v          = t == v

----------------------
-- Env
newtype Env = Env [(Sym, Type)] deriving Show

emptyEnv = Env []

extend :: Sym -> Type -> Env -> Env
extend s t (Env r) = Env $ (s, t) : r

isEmptyEnv (Env e) = e == []

---------------------
-- Substitution
substitute subst a@(TVar x)  = let res = lookup x subst
                               in if isJust res then fromJust res else a
substitute subst (t1 :-> t2) = (substitute subst t1) :-> (substitute subst t2)



substituteEnv s (Env e) = Env $ fmap (\(x, ty) -> (x, substitute s ty)) e





compose t s = fmap helper (nub $ (fst $ unzip t) ++ (fst $ unzip s))
    where
        helper x = (x, substitute t $ substitute s (TVar x))
    
---------------------
-- Algorithm Unification
unify (TVar a)    (TVar b)    
        | a == b               = []
unify a@(TVar x)  t@_         
        | not $ occurCheck a t = [(x, t)]
        | otherwise            = error  "Unification is impossible"
unify t@(l :-> s) a@(TVar x)  
        = unify a t
unify (s1 :-> s2) (l1 :-> l2)
        = unify (substitute (unify s1 l1) s2) (substitute (unify s1 l1) l2) `compose` unify s1 l1


------------------------
-- Building restrictions

-- names generator
allStrings = [ c : s| s <- "" : allStrings, c <- ['a'..'z']]

getVarName num = fromJust $ lookup num $ zip [0..] allStrings


getRests state term ty = evalState (buildRest state term ty) state

buildRest state@(Env e, last) (Var x) ty 
                                = do 
                                    let mty1 = lookup x e 
                                    put state
                                    if isJust mty1 then return [(ty, fromJust mty1)] else error "free var has undefined type"
buildRest state@(env, last) (m :@ n) ty
                                = do
                                    let ty1   = TVar $ getVarName last
                                    put state
                                    modify $ \ (e,l) -> (e,l + 1)
                                    state' <- get
                                    res <- buildRest state' m (ty1 :-> ty)
                                    state''<- get
                                    res'<- buildRest state'' n ty1
                                    return $ res ++ res'

buildRest state@(env, last) (Lam x m) ty
                                = do
                                    let ty1   = TVar $ getVarName last
                                        ty2   = TVar $ getVarName (last + 1)
                                    put state
                                    modify $ \ (e, l) ->(extend x ty1 e, l + 2)
                                    state' <- get
                                    res <- buildRest state' m ty2
                                    return $ res ++ [(ty1 :-> ty2, ty)]



-------------------------
-- Inferring type (PP, PT)

inferType term 
            = let state = initContext term
                  last' = snd state + 1
                  ty    = TVar $ getVarName $ snd state
                  state'= (fst state, last')
                  e     = unzip $ getRests state' term ty
                  t1    = foldr1 (\t1 t2 -> t1 :-> t2) $ fst e 
                  t2    = foldr1 (\t1 t2 -> t1 :-> t2) $ snd e
                  s     = unify t1 t2
              in if (isEmptyEnv $ fst state') then (Nothing, substitute s ty) else (Just $ substituteEnv s $ fst state', substitute s ty)
                where
                    initContext term = foldl' (\(env, last) x -> let last' = last + 1 in (extend x (TVar $ getVarName last) env, last')) (emptyEnv, 0) (freeVars term)

