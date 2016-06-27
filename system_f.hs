--  This implements the AST stuff for System F (no parser).
import Control.Applicative

import Test.QuickCheck 
import Test.QuickCheck.Function

import System.Random

import qualified Data.Map as Map
import qualified Data.Set as Set

type Id = String

data Typ = TVar Id              -- tau
         | TArr Typ Typ         -- tau -> tau'
         | TAll Id Typ          -- \forall t. tau
         deriving (Eq, Ord)

instance Show Typ where
  show (TVar x)   = id x
  show (TArr tau tau') = "(" ++ show tau ++ " --> " ++ show tau' ++ ")"
  show (TAll t tau) = "\\forall "++ id t ++ ". " ++ show tau

data Expr = EVar Id Typ         -- x : tau
          | ELam Id Expr Typ    -- \x e : tau
          | EApp Expr Expr Typ  -- e e : tau
          | TLam Id Expr        -- _/\_ t. (e: tau) [: \forall t. tau]
          | TApp Expr Typ       -- e[tau'] 
          deriving (Eq)

instance Show Expr where
  show (EVar x t) = "(" ++ id x ++ " : " ++ show t ++ ")"
  show (ELam x e t) =
    case t of
      TArr t' _ -> "(\\" ++ id x ++":"++show t'++" -> " ++ show e ++ ") : " ++ show t
      TVar _ -> error "shit1"
      TAll _ _ -> error "shit2"
  show (EApp e e' t) = "(" ++ show e ++" "++ show e' ++ ") : " ++ show t
  show (TLam x e) = "(_/\\_ " ++ id x ++ "." ++ show e ++") : " ++ show (TAll x (get_type e))
  show (TApp e tau) = "(" ++ show e ++ "[" ++ show tau ++ "])"


type TypContext = Set.Set Id

type VarContext = Map.Map Id Typ


-- Create the well-typed relation to ensure that the built-up expression typechecks.
well_typed :: TypContext -> VarContext -> Expr -> (Bool, Maybe Typ)
well_typed delta gamma (EVar x tau@(TAll t tau')) =
  (well_formed (Set.insert t delta) tau, Just tau')
well_typed delta gamma (EVar x tau) =
  case Map.lookup x gamma of
    Nothing -> error $ id x ++ " not in " ++ show gamma
    t       -> (True, t)
well_typed delta gamma (ELam x e tarr@(TArr t t')) =
  if well_formed delta t
    && get_type(e) == t'
    && fst(well_typed delta (Map.insert x t' gamma) e)
  then ( True, Just tarr)
  else error $ "ELam broke on " ++ show e
well_typed delta gamma (EApp e e' taus) =
    let tin' = get_type e' in
      let (wt, t) = well_typed delta gamma e in
        if (not wt) || (t == Nothing)
        then (wt, t)
        else
          case t of
            Just (TArr tin tout) -> 
              let wt' = tin == tin' && tout == taus && wt' in
                (wt', Just taus)
            Just t -> error $  "Expected a function type, got " ++ show t
            Nothing -> error "EApp broke"
well_typed delta gamma (TLam t e) =
   let (wt, mtau) = well_typed (Set.insert t delta) gamma e in
     case (wt,mtau) of
       (True, Just tau) -> (True, Just $ TAll t tau)
       (_   , _       ) -> error $ "TLam Broke on " ++ show e

well_typed delta gamma (TApp e tau) =
  let (wt,subtyp) = well_typed delta gamma e in
    case subtyp of
      Just (TAll t tau') -> (wt && well_formed delta tau,
                             Just $ typ_subst tau t tau')                        
      Just _   -> (False, Nothing)
      Nothing  -> (False, Nothing)
                            
well_typed _ _ _ = (False, Nothing)


eval_by_value :: Expr -> Expr
eval_by_value (EApp earr@(ELam x e tarr) e' t) =
  if value e'
  then eval_by_value $ subst e' x e               -- substitution
  else eval_by_value (EApp earr (eval_by_value e')t) -- congruence
eval_by_value (TApp (TLam tvar e) t) =
  eval_by_value $ tsubst t tvar e                 -- substitution
eval_by_value (TApp e t) =
  eval_by_value $ TApp (eval_by_value e) t        -- congruence
  

subst :: Expr -> Id -> Expr -> Expr
subst e x e'@(EVar y _ )   = if x == y then e else e'
subst e x e'@(ELam y e'' t) = if x == y then e' else ELam y (subst e x e'') t
subst e x e'@(EApp exp exp' t) =
  let subst' = subst e x in
    (EApp (subst' exp) (subst' exp') t)
subst e x e'@(TLam t e'') = TLam t $ subst e x e''
subst e x e'@(TApp e'' t) = TApp (subst e x e'') t


-- this performs a type substitution, recursing on terms and calling typ_subst
-- to recurse on  types
tsubst :: Typ -> Id ->  Expr -> Expr
tsubst tau t e@(EVar x t')      = EVar x $ typ_subst tau t t'
tsubst tau t e@(ELam x e' t')   = ELam x (tsubst tau t e') $ typ_subst tau t t'
tsubst tau t e@(EApp e' e'' t') = EApp (tsubst tau t e')
                                       (tsubst tau t e'')
                                       $ typ_subst tau t t'
                                  
tsubst tau t e@(TLam t' e') = if t == t' then e else TLam t' $ tsubst tau t e'
tsubst tau t e@(TApp e' t') = TApp (tsubst tau t e') (typ_subst tau t t')


-- A helper function that traverses the type formation tree
typ_subst tau t (TVar t') = if t == t'
                            then tau
                            else (TVar t')
typ_subst tau t (TArr tau' tau'') = TArr (typ_subst tau t tau')
                                         (typ_subst tau t tau'')
typ_subst tau t (TAll t' tau') =  if t == t'
                                  then (TAll t' tau)
                                  else (TAll t' $ typ_subst tau t tau)

value :: Expr -> Bool
value (EVar _ _ ) = True
value (ELam _ _ _ ) = True
value _ = False
  
  
well_formed :: TypContext -> Typ-> Bool
well_formed delta (TVar t) = Set.member t delta
well_formed delta (TArr t t') = well_formed delta t
                                && well_formed delta t'
well_formed delta (TAll x t) =  well_formed (Set.insert x delta) t

get_type :: Expr -> Typ
get_type (EVar _ t) = t
get_type (ELam _ _ t) = t
get_type (EApp _ _ t) = t
get_type (TLam t e) = TAll t (get_type e)
get_type (TApp (TLam t e) typ) = get_type (tsubst typ t e)
get_type (TApp _ _) = error "Cannot find the type for the given TypeAppliation"

--- QuickCheck Generation of Arbitrary Well-Typed System F terms
vars :: Gen Id
vars = elements $ [[c] | c <- ['a'..'z']]


--- randomly generate a set of type variables
var_prims :: Typ -> Gen Expr
var_prims t = elements [ELam "id" (EVar "id" t) $ TArr t t,
                    ELam "t" (ELam "f" (EVar "t" t) $ TArr t t) (TArr t $ TArr t t),
                    ELam "t" (ELam "f" (EVar "f" t) $ TArr t t) (TArr t $ TArr t t)
                  ]

typ_prims :: [Id]
typ_prims = ["tau", "phi", "sigma", "nat", "bool"]

sys_type :: Gen Typ
sys_type = resize 1 $ sized (typ [])
  where
    typ :: Integral a => [Id] -> a -> Gen Typ
    typ []      0 = error "Cannot create a variable with no inputs"
    typ []      n = do v <- vars
                       t <- typ [v] (n-1)
                       return (TAll v t)
    typ symbols 0 = TVar <$> (elements symbols)
    typ symbols n =        
      oneof [ TVar <$> (elements symbols),
              let smaller = typ symbols (n `div` 2) in
                liftA2 TArr smaller smaller,
              do
                v <- vars
                t <- typ (v:symbols) (n-1)
                return (TAll v t)
            ]



ident t= ELam "*" (EVar "*" t) (TArr t t)


sys_term :: Gen Expr
sys_term = resize 1 $ sys_type >>= (sized . typ_terms)
  where
    typ_terms :: Integral a => Typ -> a -> Gen Expr
    typ_terms t 0 = var_prims t -- Deterministic Cases w.r.t type structure
    typ_terms t@(TArr _ tout) n =
      do v <- vars 
         body <- typ_terms tout (n-1)
         return $ ELam v body t
    typ_terms (TAll tid tau) n =
      (TLam tid) <$> (typ_terms tau (n-1))

    -- ND Case. Chose EVar, EApp, or TApp(TLam)
    typ_terms tau n =
      let exprs =  [(\x -> EVar x tau) <$> vars,
                     do arg_type <- sys_type
                        verb <- typ_terms (TArr arg_type tau) (n `div` 2)
                        noun <- typ_terms arg_type (n `div` 2)
                        return $ EApp verb noun tau
                   ] in
      if n < 2 then oneof exprs
      else
        do tid <- vars
           (new_type, la_type) <- make_app_type tid tau
           la_expr <- typ_terms la_type (n-2)
           return $ TApp (TLam tid la_expr) new_type   

make_app_type :: Id -> Typ -> Gen (Typ,Typ)
make_app_type tvar goal_type =
  let subs = Set.toList $ subtypes goal_type in
    do hole <- elements subs
       return $ (hole, replace hole (TVar tvar) goal_type)

subtypes :: Typ -> Set.Set Typ
subtypes tau@(TVar x)   = Set.singleton tau
subtypes tau@(TArr t t') = Set.union (Set.singleton tau)
                          $ Set.union (subtypes t) (subtypes t')
subtypes tau@(TAll x t) = Set.union (Set.singleton tau)
                          $ Set.difference (subtypes t)
                            $ Set.singleton (TVar x)

replace :: Typ -> Typ -> Typ -> Typ
replace hole tau t@(TVar x) = if hole == t then tau else t
replace hole tau t@(TArr t' t'') =
  if hole == t then tau else
    let smaller = replace hole tau in
      TArr (smaller t') (smaller t'')
replace hole tau t@(TAll x t') = if hole == t then tau else t -- is this right?

instance Arbitrary Expr where
  arbitrary = sys_term

prop_wellTyped :: Expr -> Bool
prop_wellTyped = fst . (well_typed Set.empty Map.empty)

valid_term :: Property
valid_term =
  forAll sys_term $ \e ->
    well_formed Set.empty (get_type e)==> prop_wellTyped e
