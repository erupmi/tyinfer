module MinHS.TyInfer where

import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Subst
import MinHS.TCMonad

import Data.Monoid (Monoid (..), (<>))
import Data.Foldable (foldMap)
import Data.List (nub, union, (\\))

primOpType :: Op -> QType
primOpType Gt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ge   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Lt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Le   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Eq   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ne   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Neg  = Ty $ Base Int `Arrow` Base Int
primOpType Fst  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "a"
primOpType Snd  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "b"
primOpType _    = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Int)

constType :: Id -> Maybe QType
constType "True"  = Just $ Ty $ Base Bool
constType "False" = Just $ Ty $ Base Bool
constType "()"    = Just $ Ty $ Base Unit
constType "Pair"  = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "b" `Arrow` (TypeVar "a" `Prod` TypeVar "b"))
constType "Inl"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType "Inr"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "b" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType _       = Nothing

type Gamma = E.Env QType

initialGamma :: Gamma
initialGamma = E.empty

tv :: Type -> [Id]
tv = tv'
 where
   tv' (TypeVar x) = [x]
   tv' (Prod  a b) = tv a `union` tv b
   tv' (Sum   a b) = tv a `union` tv b
   tv' (Arrow a b) = tv a `union` tv b
   tv' (Base c   ) = []

tvQ :: QType -> [Id]
tvQ (Forall x t) = filter (/= x) $ tvQ t
tvQ (Ty t) = tv t

tvGamma :: Gamma -> [Id]
tvGamma = nub . foldMap tvQ

infer :: Program -> Either TypeError Program
infer program = do (p',tau, s) <- runTC $ inferProgram initialGamma program
                   return p'

unquantify :: QType -> TC Type
{-
Normally this implementation would be possible:

unquantify (Ty t) = return t
unquantify (Forall x t) = do x' <- fresh
                             unquantify (substQType (x =:x') t)

However as our "fresh" names are not checked for collisions with names bound in the type
we avoid capture entirely by first replacing each bound
variable with a guaranteed non-colliding variable with a numeric name,
and then substituting those numeric names for our normal fresh variables
-}

unquantify = unquantify' 0 emptySubst
unquantify' :: Int -> Subst -> QType -> TC Type
unquantify' i s (Ty t) = return $ substitute s t
unquantify' i s (Forall x t) = do x' <- fresh
                                  unquantify' (i + 1)
                                              ((show i =: x') <> s)
                                              (substQType (x =:TypeVar (show i)) t)

unify :: Type -> Type -> TC Subst
unify (TypeVar v1) (TypeVar v2)
  | v1 == v2 = return emptySubst
  | otherwise = return (v1 =: (TypeVar v2))
unify (Base v1) (Base v2)
  | v1 == v2 = return emptySubst
  | otherwise = typeError (TypeMismatch (Base v1) (Base v2))
unify (Prod v11 v12) (Prod v21 v22) = do
  g <- unify v11 v21
  let res1 = substitute g v12
      res2 = substitute g v22
  g' <- unify res1 res2
  return (g <> g')
unify (Sum v11 v12) (Sum v21 v22) = do
  g <- unify v11 v21
  let res1 = substitute g v12
      res2 = substitute g v22
  g' <- unify res1 res2
  return (g <> g')
unify (Arrow v11 v12) (Arrow v21 v22) = do
  g <- unify v11 v21
  let res1 = substitute g v12
      res2 = substitute g v22
  g' <- unify res1 res2
  return (g <> g')
unify (TypeVar v) t
  | hasOccur v t = typeError (OccursCheckFailed v t)
  | otherwise = return (v =: t)
unify t (TypeVar v)
  | hasOccur v t = typeError (OccursCheckFailed v t)
  | otherwise = return (v =: t)
unify t1 t2 = typeError (TypeMismatch t1 t2)

hasOccur :: Id -> Type -> Bool
hasOccur t (TypeVar x)
  | t == x = True
  | otherwise = False
hasOccur t (Sum x y) = (hasOccur t x) || (hasOccur t y)
hasOccur t (Prod x y) = (hasOccur t x) || (hasOccur t y)
hasOccur t (Arrow x y) = (hasOccur t x) || (hasOccur t y)
hasOccur t (Base _) = False

generalise :: Gamma -> Type -> QType
generalise g t =
  let res = (tvQ (Ty t)) \\ (tvGamma g)
  in expand res t

expand :: [Id] -> Type -> QType
expand [] t = Ty t
expand (hd:tl) t =
  Forall hd (expand tl t)

inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)
inferProgram g [Bind name _ [] e] = do
  (e', tau, tee) <- inferExp g e
  let res = substitute tee tau
      fin = generalise g res
  case fin of
    Ty t  ->
      let p' = [Bind name (Just (Ty res)) [] e']
          p'' = map (allTypesBind (substQType tee)) p'
      in return (p'', res, tee)
    t'    ->
      let p' = [Bind name (Just t') [] e']
          p'' = map (allTypesBind (substQType tee)) p'
      in return (p'', res, tee)

inferExp :: Gamma -> Exp -> TC (Exp, Type, Subst)
-- -- Note: this is the only case you need to handle for case expressions
-- inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2])
-- inferExp g (Case e _) = typeError MalformedAlternatives
-- Constants and Variables
inferExp g (Num n) = do
  return (Num n, Base Int, emptySubst)
inferExp g (Var id) =
  let var = E.lookup g id
  in case var of
    Just res -> do
      res' <- unquantify res
      return (Var id, res', emptySubst)
    Nothing -> typeError (NoSuchVariable id)
-- Constructors and Primops
inferExp g (Con id) =
  let con = constType id
  in case con of
    Just res -> do
      res' <- unquantify res
      return (Con id, res', emptySubst)
    Nothing -> typeError (NoSuchConstructor id)
inferExp g (Prim op) = do
      res <- unquantify (primOpType op)
      return (Prim op, res, emptySubst)
-- Application
inferExp g (App e1 e2) = do
  (e1', tau1, tee) <- inferExp g e1
  (e2', tau2, tee') <- inferExp (substGamma tee g) e2
  alpha <- fresh
  let lhs = substitute tee' tau1
      rhs = tau2 `Arrow` alpha
  u <- unify lhs rhs
  let sub = u <> tee' <> tee
  return (App e1' e2', substitute u alpha, sub)
-- If-Then-Else
inferExp g (If e e1 e2) = do
  (e', tau, tee) <- inferExp g e
  u <- unify tau (Base Bool)
  let g' = substGamma (u <> tee) g
  (e1', tau1, tee1) <- inferExp g' e1
  let g'' = substGamma (tee1 <> u <> tee) g
  (e2', tau2, tee2) <- inferExp g'' e2
  u' <- unify (substitute tee2 tau1) tau2
  let sub = u' <> tee2 <> tee1 <> u <> tee
  return (If e' e1' e2', substitute u' tau2, sub)
-- Case
inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2]) = do
  (e', tau, tee) <- inferExp g e
  alpha_l <- fresh
  let g' = substGamma tee (E.add g (x, Ty alpha_l))
  (e1', tau_l, tee1) <- inferExp g' e1
  alpha_r <- fresh
  let g'' = substGamma (tee1 <> tee) (E.add g (y, Ty alpha_r))
  (e2', tau_r, tee2) <- inferExp g'' e2
  let lhs1 = substitute (tee2 <> tee1 <> tee) (Sum alpha_l alpha_r)
      rhs1 = substitute (tee2 <> tee1) tau
  u <- unify lhs1 rhs1
  let lhs2 = substitute (u <> tee2) tau_l
      rhs2 = substitute u tau_r
  u' <- unify lhs2 rhs2
  let sub = u' <> u <> tee2 <> tee1 <> tee
  return (Case e' [Alt "Inl" [x] e1', Alt "Inr" [y] e2'], substitute (u' <> u) tau_r, sub)
inferExp g (Case e _) = typeError MalformedAlternatives
-- Recursive Functions
inferExp g (Recfun (Bind f _ [x] e)) = do
  alpha_1 <- fresh
  alpha_2 <- fresh
  let g' = E.addAll g [(x, Ty alpha_1), (f, Ty alpha_2)]
  (e', tau, tee) <- inferExp g' e
  let lhs = substitute tee alpha_2
      rhs = (substitute tee alpha_1) `Arrow` tau
  u <- unify lhs rhs
  let sub = u <> tee
      ret = substitute u rhs
  return (Recfun (Bind f (Just (Ty ret)) [x] e'), ret, sub)
inferExp g (Recfun _) = typeError ForallInRecfun
-- Let Bindings
inferExp g (Let [Bind x _ _ e1] e2) = do
  (e1', tau, tee) <- inferExp g e1
  let tmp = substGamma tee g
      gen = generalise tmp tau
      g' = E.add g (x, gen)
  (e2', tau', tee') <- inferExp g' e2
  let sub = tee' <> tee
  return (Let [Bind x (Just gen) [] e1'] e2', tau', sub)
inferExp g (Let _ _) = typeError ForallInRecfun
