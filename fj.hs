-- Create an AST for Featherweight Jvava, small-step evaluation, and typing system

import qualified Data.Map.Strict as Map


-- Below is the basis of the syntax tree
type Id = String
type ClassName = String
type FieldName = String
type MethodName = String

data Class =
  Object
  | Class ClassName Class [Field] Constructor [Method]
  deriving (Eq, Ord, Show)
         -- class C0 extends C1 {Cbar fbar ; K Mbar}

data Constructor = Constructor Class [Field] deriving (Eq, Ord, Show)
data Method = Method Class MethodName [Field] Expr deriving (Eq, Ord, Show)
data Expr =
    Var  Id
  | FAcc Expr FieldName          -- Field Access
  | MAcc Expr  MethodName [Expr]  -- Method Access
  | New  Class [Expr]             -- New Object
  | Cast Class Expr               -- Cast to new class
    deriving (Eq, Ord, Show)

data Field = Field Class FieldName deriving (Eq, Ord, Show) -- (Class Field name)

data Typ =
  TClass Class
  | TMethod [Typ] Class
  deriving(Eq, Ord, Show)


type ClassTable = Map.Map Class Class

isSubtype :: ClassTable -> Class -> Class -> Bool
isSubtype ct c@(Class cname (Class cname' _ _ _ _) _ _ _) d@(Class dname _ _ _ _)
  | c == d = True
  | cname' == dname = True
  | c /= d =
      case (Map.lookup c ct) of
        Just (Class cn (Class dn _ _ _ _) _ _ _ ) ->
          if cn == cname  && dn == dname then True
          else foldr (\cls rst ->
                       rst || (isSubtype ct c cls && isSubtype ct cls c)
                     ) False (Map.keys ct)
        Nothing -> False

-- Field Lookup
fields :: ClassTable -> Class -> [Field]
fields ct Object = []
fields ct (Class c dCls fs _ _) =
  case dCls of
    Object -> fs
    (Class d _ _ _ _) -> fs ++ (fields ct dCls)
    
-- Method type lookup
mtype :: ClassTable -> MethodName -> Class -> Maybe Typ
mtype ct m (Object) = Nothing
mtype ct m (Class c d _ _ ms) =
  if methodIn m ms
  then
    let (paramTypes, returnClass) = foldr (getParamTypes m) ([], Object) ms in
    Just $ TMethod paramTypes returnClass
  else
   mtype ct m d 
  where
    getParamTypes :: MethodName -> Method -> ([Typ],Class) -> ([Typ],Class)
    getParamTypes m (Method cls m' params _) p =
      if m == m'
      then let (pms, _) = p in
           ((map getFieldClass params) ++ pms, cls)
      else p


methodIn :: MethodName -> [Method] -> Bool
methodIn m = foldr (\(Method _ m' _ _ ) b -> m == m' || b) False  

getFieldClass :: Field -> Typ
getFieldClass (Field cn fn) = TClass cn
           
