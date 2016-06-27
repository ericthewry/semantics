-- This is simply a file to set up the simply typed lambda calculus, and
-- generate terms within it

type Id = String

data Typ =
    TNat
  | TBool
  | Arrow Typ Typ
  deriving (Eq)

instance Show Typ where
  show (TNat) = "nat"
  show (TBool) = "bool"
  show (Arrow t t') = "(" ++ show t ++ "->" ++ show t' ++ ")"
    
data Expr = Var Id Typ
  | Lam Id Expr Typ
  | App Expr Expr Typ
  deriving (Eq)

instance Show Expr where
  show (Lam x e (Arrow t _)) = "(\\" ++ show x ++ " : " ++ (show t) ++ ". " ++ (show e) ++ ")"
  show (App e e' t) = "(" ++ show e ++ " " ++ show e' ++ " : " ++ show t ++ ")"
  show (Var x t) = "(" ++ show x ++ " : " ++ show  t ++ ")"

example :: Expr
-- example = App (Lam "x" (Var "1" TNat) (Arrow TBool TNat)) (Var "y" TBool) TNat
example = App (Lam "x" body (Arrow TNat TNat) ) (Var "1" TNat) TNat

body = (App
         (Lam "y"
           (Var "y" (Arrow TNat TNat))
           (Arrow (Arrow TNat TNat) (Arrow TNat TNat)))
         (Lam "x"
           (Var "x" (Arrow TNat TNat))
           (Arrow (Arrow TNat TNat) (Arrow TNat TNat)))
         (Arrow TNat TNat)
       )

          
-- Assume closed terms.. This is call by value.
small_step (Lam x e (Arrow t t')) =
  if get_type(e) == t then small_step e else error "Type Mismatch, Lambda is not an arrow Type"
small_step (Lam x e _ ) = error "Type error : Lambda must have arrow type"
small_step (App (Lam x e (Arrow t t')) e' tt) =
  if t' == tt && t == get_type e'
  then subst e x e'
  else error "Type Mismatch: Improper application"
small_step (App e e' t) =
  if value e
  then (App e (small_step e') t) -- Congruence L
  else (App (small_step e) e' t) -- Congruence R
small_step _ = error "Cannot take a step"

get_type :: Expr -> Typ
get_type (Var _ t ) = t
get_type (Lam _ _ t) = t
get_type (App _ _ t) = t

value :: Expr -> Bool
value (Var _ _ ) = True
value (Lam _ _ _ ) = True
value _ = False

subst :: Expr -> Id -> Expr -> Expr
subst e x exp@(Var y t) = if x == y then e else exp
subst e x (App e' e'' t) = (App (subst e x e') (subst e x e'') t)
subst e x exp@(Lam y e' t) = if x == y then exp else (Lam y (subst e x e') t)


