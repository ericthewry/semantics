
-- Create an AST for System F, small-step evaluation, and an arbitrary instance
-- for quickcheck and random term generation

import           Control.Applicative
import qualified Data.Map                 as Map
import qualified Data.Set                 as Set
import           System.Random
import           Test.QuickCheck
import           Test.QuickCheck.Function

-- Variable identifiers for both types and expressions
type Id = String

-- The Types for the expressions. Note that unlike Reynold's original system F
-- there is no `int` or `nat` type (See Robert Harpers PFPL text for
-- justification)
data Typ = TVar Id              -- tau
         | TArr Typ Typ         -- tau -> tau'
         | TAll Id Typ          -- \forall t. tau
         deriving (Eq, Ord, Show)

-- prettified, readable show instance
-- instance Show Typ where
--   show (TVar x)   = id x
--   show (TArr tau tau') = "(" ++ show tau ++ " --> " ++ show tau' ++ ")"
--   show (TAll t tau) = "\\forall "++ id t ++ ". " ++ show tau

--  The Expression type for system F
data Expr = EVar Id Typ         -- x : tau
          | ELam Id Expr Typ    -- \x e : tau
          | EApp Expr Expr Typ  -- e e : tau
          | TLam Id Expr        -- _/\_ t. (e: tau) [: \forall t. tau]
          | TApp Expr Typ       -- e[tau']
          deriving (Eq, Show)

--  prettified printing matching comments above
-- instance Show Ex-- pr where
   -- show (EVar x t) = "(" ++ id x ++ " : " ++ show t ++ ")"
   -- show (ELam x e t) =
   --   case t of
   --     TArr t' _ -> "(\\" ++ id x ++":"++show t'++" -> " ++ show e ++ ") : " ++ show t
   --     TVar _ -> error "shit1"
   --     TAll _ _ -> error "shit2"
   -- show (EApp e e' t) = "(" ++ show e ++" "++ show e' ++ ") : " ++ show t
   -- show (TLam x e) = "(_/\\_ " ++ id x ++ "." ++ show e ++") : " ++ show (TAll x (get_type e))
   -- show (TApp e tau
        -- ) = "((" ++ show e ++ ")[" ++ show tau ++ "])"


type TypContext = Set.Set Id     -- Traditionally represented as \Delta
type VarContext = Map.Map Id Typ -- Traditionally represented as \Gamma


-- Create the well-typed relation to ensure that the built-up expression typechecks.
well_typed :: TypContext -> VarContext -> Expr -> (Bool, Maybe Typ)
well_typed del _ (EVar x tau@(TAll t tau')) =
  (isa_type (Set.insert t del) tau, Just tau')
well_typed del gam (EVar x tau) =
  case Map.lookup x gam of
    Nothing ->
      error
      $ "Term " ++ id x ++ " has no type : " ++ show tau ++ " in " ++ (show gam)
    Just t  ->
      if t == tau then (True, Just t)
      else error $ "Type Mismatch: " ++ id x ++ " : " ++ show t ++ " should have type " ++ show tau 
well_typed del gam (ELam x e tarr@(TArr tin taus)) =
  let wt = fst (well_typed del (Map.insert x tin gam) e) in
  if isa_type del tin && get_type e == taus && wt
  then (True, Just tarr)
  else (False, Nothing)
well_typed delta gamma (EApp e e' taus) =
    let (wt', mtin') = well_typed delta gamma e' in
      let (wt, t) = well_typed delta gamma e in
        if not $ wt && wt' then (wt, t)
        else case (t,mtin') of
          (Just (TArr tin tout), Just tin') ->
            let wt'' = tin == tin' && tout == taus && wt' in
              (wt'', Just taus)

          (Just t, _) -> error $  "Expected a function type, got " ++ show t
          (Nothing, _) -> error "EApp broke"
well_typed del gam (TLam t e) =
   let (wt, mtau) = well_typed (Set.insert t del) gam e in
     case (wt,mtau) of
       (True, Just tau) -> (True, Just $ TAll t tau)
       (_   , _       ) -> (False, Nothing)  --error $ "TLam Broke on " ++ show e

well_typed delta gamma (TApp e tau) =
  let (wt,subtyp) = well_typed delta gamma e in
    case subtyp of
      Just (TAll t tau') -> (wt && isa_type delta tau,
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


isa_type :: TypContext -> Typ-> Bool
isa_type delta (TVar t) = Set.member t delta
isa_type delta (TArr t t') = isa_type delta t
                                && isa_type delta t'
isa_type delta (TAll x t) =  isa_type (Set.insert x delta) t

get_type :: Expr -> Typ
get_type (EVar _ t) = t
get_type (ELam _ _ t) = t
get_type (EApp _ _ t) = t
get_type (TLam t e) = TAll t (get_type e)
get_type (TApp (TLam t e) typ) = get_type (tsubst typ t e)
get_type (TApp _ _) = error "Cannot find the type for the given TypeAppliation"

--- QuickCheck Generation of Arbitrary Well-Typed System F terms


universe :: [Id]
universe = [[c] | c <- ['a' .. 'z']]

vars :: Gen Id
vars = elements universe


--- randomly generate a set of type variables
var_prims :: Typ -> Gen Expr
var_prims t = elements [ELam "id" (EVar "id" t) $ TArr t t,
                    ELam "t" (ELam "f" (EVar "t" t) $ TArr t t) (TArr t $ TArr t t),
                    ELam "t" (ELam "f" (EVar "f" t) $ TArr t t) (TArr t $ TArr t t)
                  ]

typ_prims :: [Id]
typ_prims = ["tau", "phi", "sigma", "nat", "bool"]

sys_type :: Int -> Gen Typ
sys_type sz = resize sz $ sized (typ [])
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
                v <- elements $ typ_prims
                t <- typ (v:symbols) (n-1)
                return (TAll v t)
            ]



ident t= ELam "*" (EVar "*" t) (TArr t t)

scope :: VarContext -> Gen Id
scope m =
  let ls = Set.toList $ Set.fromList $ map fst $ Map.toList m in
    if length ls <= 0 then error "EMPTY LIST" else
      elements ls

swp f a b = f b a


f_term :: Gen Expr
f_term = resize 10 $ (sys_type 10) >>= (sized . (typ_terms Map.empty))

typ_terms :: VarContext -> Typ -> Int -> Gen Expr
typ_terms gam t 0 =
  if gam == Map.empty
  then case t of            -- if you cannot create a term, extend the generator
         (TVar _) -> error "Cannot create variable in empty ctx"
         (TArr ti to) -> typ_terms gam t 1
         (TAll tid t) -> typ_terms gam t 1
  else evargen gam t

-- ND Case. Chose EVar, EApp, or TApp(TLam)
typ_terms gam tau@(TVar _) n = if gam == Map.empty
                               then eappgen gam tau n
                               else do tid <- vars
                                       oneof [evargen gam tau]
                                              -- eappgen gam tau n,
                                              -- tappgen gam tau n]
typ_terms gam tau@(TArr tin tout) n = if gam == Map.empty
                                      then oneof[elamgen gam tin tout n]
                                                 -- eappgen gam tau n
                                                 -- tappgen gam tau n
                                                -- ]
                                      else
                                         -- oneof [evargen gam tau  ,
                                                elamgen gam tin tout n
                                                -- eappgen gam tau n,
                                                -- tappgen gam tau n]

typ_terms gam tau@(TAll tid tau') n = oneof [tlamgen gam tid  tau'     n]
                                               -- eappgen gam           tau n,
                                               -- tappgen gam           tau n]

evargen :: VarContext -> Typ -> Gen Expr
evargen gam tau =
  let valid_scope = map fst $ filter (\(e,tau') -> tau == tau') $ Map.toList gam in
    if length valid_scope <= 0
    then error $ "Invalid Scope (" ++ show gam ++") for : " ++ show tau
    else swp EVar tau <$> elements valid_scope

elamgen :: VarContext -> Typ -> Typ -> Int -> Gen Expr
elamgen gam tin taus n = let used_vars = Set.fromList $ map fst $ Map.toList gam in
                           let fresh_vars = Set.difference (Set.fromList universe) used_vars in
                             do fresh <- elements $ Set.toList fresh_vars
                                exp   <- typ_terms (Map.insert fresh tin gam) taus $ n-1
                                return $ ELam fresh exp $ TArr tin taus

eappgen :: VarContext -> Typ -> Int -> Gen Expr
eappgen gam tau n =  do arg_type <- sys_type 1
                        e  <- typ_terms gam (TArr arg_type tau) $ n `div` 2
                        e' <- typ_terms gam arg_type            $ n `div` 2
                        return $ EApp e e' tau

tappgen :: VarContext -> Typ -> Int -> Gen Expr
tappgen gam tau n = do tid <- vars -- get a new variable identifier
                       (new_type, la_type) <- make_app_type tid tau
                       la_expr <- typ_terms gam la_type n
                       return $ TApp (TLam tid la_expr) new_type

tlamgen :: VarContext -> Id -> Typ -> Int -> Gen Expr
tlamgen gam tid tau n = (TLam tid) <$> (typ_terms gam tau $ n-1)



make_app_type :: Id -> Typ -> Gen (Typ,Typ)
make_app_type tvar goal_type =
  let subs = Set.toList $ subtypes goal_type in
    do hole <- elements subs
       return $ (hole, replace hole (TVar tvar) goal_type)

subtypes :: Typ -> Set.Set Typ
subtypes tau@(TVar x)   = Set.singleton tau
subtypes tau@(TArr t t') = Set.union (Set.singleton tau)
                          $ Set.union (subtypes t) (subtypes t')
subtypes tau@(TAll x t) = Set.union (Set.singleton tau) $ Set.difference (subtypes t)
                            $ Set.singleton (TVar x)

replace :: Typ -> Typ -> Typ -> Typ
replace hole tau t@(TVar x) = if hole == t then tau else t
replace hole tau t@(TArr t' t'') =
  if hole == t then tau else
    let smaller = replace hole tau in
      TArr (smaller t') (smaller t'')
replace hole tau t@(TAll x t') = if hole == t
                                 then tau
                                 else t -- is this right? if its wrong its an underfit

instance Arbitrary Expr where
  arbitrary = f_term

instance Arbitrary Typ where
  arbitrary = resize 10 $ sized sys_type

prop_wellTyped :: Expr -> Bool
prop_wellTyped = fst . (well_typed Set.empty Map.empty)

valid_term :: Property
valid_term =
  forAll f_term $ \e ->
    isa_type Set.empty (get_type e)==> prop_wellTyped e

term = quickCheck isa_type
okay = quickCheck valid_term

dup f a = f a a

mkctx :: ([String], VarContext, TypContext)
mkctx = 
  let syms = [[c] | c <- ['a' .. 'z']] in
  let gam = Map.fromList $ zip syms $ map TVar syms in
  let del = Set.fromList syms in
    (syms, gam, del)

evartest :: Gen Expr
evartest =
  let (s, g, d) = mkctx in 
      (sys_type 2) >>= (evargen g)
         

elamtest :: Gen Expr
elamtest =
  let (_, g, d) = mkctx in
  do tin <- sys_type 3
     tout <- sys_type 3
     n <- choose (0,4)
     elamgen Map.empty tin tout n

bigcheck = (quickCheckWith stdArgs {maxSuccess = 5000})

wf :: Gen Expr -> IO ()
wf = bigcheck . wf_ge
  where
    wf_ge :: Gen Expr -> Gen Bool
    wf_ge ge =
      let (_, g, d) = mkctx in
        do e <- ge
           return $ fst $ well_typed d g e

