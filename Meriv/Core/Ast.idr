module Meriv.Core.Ast

import Data.List
import Meriv.Core.Util

-- Schema definition

||| Data needed to define an entity
||| of a particular type.
data EntityDec : (ts : List Nat) -> Type where
  MkEntityDec : Nat -> ( t : Nat ) -> { auto p: t `elem` ts = True } -> EntityDec ts

identifier : EntityDec ts -> Nat
identifier (MkEntityDec i _) = i

type : EntityDec ts -> Nat
type (MkEntityDec _ t) = t

Eq (EntityDec ts) where
  (MkEntityDec x y) == (MkEntityDec z w) = 
    x == z && y == w
    
||| Data needed to declare that a type is a 
||| subtype of some other type.
data SubtypeDec : (ts : List Nat) -> Type where
  MkSubtypeDec : 
      (subtype : Nat) 
   -> { auto p1: subtype `elem` ts = True } 
   -> (supertype : Nat) 
   -> { auto p2: supertype `elem` ts = True }
   -> SubtypeDec ts

Eq (SubtypeDec ts) where
  (MkSubtypeDec x y) == (MkSubtypeDec z w) = 
    x == z && y == w

||| Modes for Meriv relational arguments.
data ModeDecl =
    InM 
  | OutM 
  | BothM

Eq ModeDecl where
  InM   == InM   = True
  OutM  == OutM  = True
  BothM == BothM = True
  _ == _         = False

mutual
  ||| Part of a Meriv Schema needed for typechecking.
  record MvBaseSchema where
    constructor MkBaseSchema
    extends     : Maybe MvBaseSchema
    types'       : List Nat
    subtypes'    : List (SubtypeDec types')
    entities'    : List (EntityDec types')
    relations'   : case extends of
      Just base => List (RelDecl base)
      Nothing   => ()
    rules'       : case extends of
      Just base => List (RuleDecl base)
      Nothing   => ()

    ||| Data needed to declare a Meriv relation.
  record RelDecl (s : MvBaseSchema) where
    constructor MkRelDecl
    name  : String
    argTypes : List (ModeDecl, MvType s)

  Eq (RelDecl s) where
    (MkRelDecl n xs) == (MkRelDecl m ys) = 
      xs == ys && n == m

  ||| Data needed to declare a Meriv rule.
  record RuleDecl (s : MvBaseSchema) where
    constructor MkRuleDecl
    -- TODO: Fix this after implementing terms
    clauses : ()

  Eq (RuleDecl s) where
    (MkRuleDecl _) == (MkRuleDecl _) = 
      True
  
  types : (base: MvBaseSchema) -> List Nat
  types base = base.types' ++ maybe [] types base.extends
  
  -- TODO: I think I need to use a lemma here to supply the proof manually
  subtypes : (base: MvBaseSchema) -> List (SubtypeDec (types base))
  subtypes base = base.subtypes' ++ maybe [] subtypes base.extends
  
  lemma_extendSubtypes : (p : subsetList xs ys) -> SubtypeDec xs -> SubtypeDec ys
  lemma_extendSubtypes = _

  entities : (base: MvBaseSchema) -> List (EntityDec (types base))
  entities base = base.entities' ++ maybe [] entities base.extends
  
  relations : (base: MvBaseSchema) -> List (RelDecl base)
  relations base = case base.extends of
    Just parent => parent.relations' ++ maybe [] relations parent.extends
    Nothing     => []
  
  rules : (base: MvBaseSchema) -> List (RelDecl base)
  rules base = case base.extends of
    Just parent => parent.rules' ++ maybe [] rules parent.extends
    Nothing     => []

  ||| Type of meriv types, given a particular schema.
  data MvType : MvBaseSchema -> Type where
    IntT    : MvType s
    StringT : MvType s
    DoubleT : MvType s
    EntityT : 
        (s : MvBaseSchema)
     -> (t : Nat)
     -> { auto p: t `elem` (types s) = True }
     -> MvType s
    RelT :
        (s : MvBaseSchema)
     -> List (ModeDecl, MvType s)
     -> MvType s
    FuncT    : 
        MvType s
     -> MvType s
     -> MvType s
    -- RuleT :
    RecordT :
        Set (String, MvType s)
     -> MvType s
    UnionT :
        Set (String, MvType s)
     -> MvType s
   
  Eq (MvType s) where
    IntT    == IntT    = True
    StringT == StringT = True
    DoubleT == DoubleT = True
    -- (EntityT x y) == (EntityT z w)
    --   = x == z && y == w
    _ == _ = False

  Ord (MvType s) where
    compare x y = EQ

||| Idris type corresponding to a Meriv entity type
||| in a schema.
data Entity : MvBaseSchema -> Nat -> Type where
  MkEntity  : 
      (s : MvBaseSchema) 
   -> (t : Nat) 
   -> { auto p: ((t `elem` types s) = True) } 
   -> Entity s t

mutual
  ||| Implementation of a simple record type for Meriv
  data Record : (f : Type -> Type) -> (s : MvBaseSchema) -> (ts: Set (String, MvType s)) -> Type where
    RNil  : Record f s (mkSet [])
    RCons : (label : String) -> MvExpr f s t -> Record f s ts -> Record f s (ts `add` (label,t))
    
  ||| Implementation of a simple union type.  
  data Union : (f : Type -> Type) -> (s : MvBaseSchema) -> (ts: Set (String, MvType s)) -> Type where
    UEmpty  : Union f s (mkSet [])
    UInj : (label : String) -> MvExpr f s t -> { auto p: (label,t) `elem` ts = True } -> Union f s ts

  data VarF : Type -> Type where
    Var    : Nat -> VarF a
    Ground : a   -> VarF a 

  data IdF : Type -> Type where
    Id : a -> IdF a

  ||| A Meriv term is a relation with arguments of types ts,
  ||| applied to a list of expressions in order, correpsonding to
  ||| the types ts.
  |||
  ||| Example:
  |||   rel likes: person, food.
  |||   nate: person.
  ||| 
  |||   likes(nate, X) is a MvTerm.
  |||
  data MvTerm : (f : Type -> Type) -> (s : MvBaseSchema) -> Type where
    MkTerm    : 
        { s : MvBaseSchema } 
     -> { ts : List (ModeDecl, MvType s) } 
     -> MvExpr f s (RelT s ts) 
     -> MvExprs f s (map (\(x,y) => y) ts) 
     -> MvTerm f s
 
  record MvClause (s : MvBaseSchema) where
    constructor MkClause 
    head : MvTerm VarF s
    body : List (MvTerm VarF s)

  data MvExprs : (f : Type -> Type) -> (s : MvBaseSchema) -> List (MvType s) -> Type where
    NilExprs : MvExprs f s []
    ConsExpr : MvExpr f s t -> MvExprs f s ts -> MvExprs f s (t :: ts)

  data MvExpr : (f : Type -> Type) -> (s : MvBaseSchema) -> MvType s -> Type where
    AppExp    : MvExpr f s (FuncT a b) -> MvExpr f s a -> MvExpr f s b
    -- QueryExp  : (q : Query s rs) -> (MvExprs IdF s rs -> MvExpr IdF s r) -> MvExpr IdF s r
    BaseExp   : f (MvBaseExpr s a) -> MvExpr f s a

  ||| Type of expressions in the Meriv language
  data MvBaseExpr : (s : MvBaseSchema) -> MvType s -> Type where
    IntExp    : Int         -> MvBaseExpr s IntT
    StringExp : String      -> MvBaseExpr s StringT
    DoubleExp : Double      -> MvBaseExpr s DoubleT
    FuncExp   : (MvBaseExpr s a -> MvBaseExpr s b) -> MvBaseExpr s (FuncT a b)
    RelExp    : 
          (s : MvBaseSchema) 
       -> (identifier: String)
       -> (ts : List (ModeDecl, MvType s))
       -> { auto p: (MkRelDecl identifier ts) `elem` (relations s) = True }
       -> MvBaseExpr s (RelT s ts)
    -- SchemaExp :
    -- RuleExp   :
    --     (s : MvBaseSchema)
    --   -> 
    RecordExp : Record s ts -> MvBaseExpr s (RecordT ts)
    UnionExp  : Union s ts  -> MvBaseExpr s (UnionT ts)
    EntityExp : 
         (s : MvBaseSchema)
      -> (e : Nat)
      -> (t : Nat)
      -> { auto p1: t `elem` (types s) = True }
      -> { auto p2: MkEntityDec e t `elem` entities s = True } 
      -> MvBaseExpr s (EntityT s t)
    InjectEntitySub : 
         (s : MvBaseSchema)
      -> (x : Nat) -> { auto p1: x `elem` (types s) = True }
      -> (y : Nat) -> { auto p2: y `elem` (types s) = True }
      -> MvBaseExpr s (EntityT s x) 
      -> MvBaseExpr s (EntityT s y)

evaluate : {s : MvBaseSchema} -> {a : MvType s} -> MvExpr IdF s a -> MvExpr IdF s a
evaluate (AppExp (FuncExp f) x) = evaluate $ f x
evaluate x = x

||| Information needed to declare an implcit conversion
||| of Meriv types.
record ConversionDec (s : MvBaseSchema) where
  constructor MkConversionDec
  fromType   : MvType s
  toType     : MvType s
  conversion : MvBaseExpr s fromType -> MvBaseExpr s toType

Eq (ConversionDec s) where
  (MkConversionDec x y _) == (MkConversionDec z w _) = 
    x == z && y == w
    
||| A full schema for the meriv language.
record MvSchema where
  constructor MkSchema
  base  : MvBaseSchema
  conversions : List (ConversionDec base)

||| Evidential subtype relation for Meriv types.
data Subtype : (s : MvSchema) -> MvType (base s) -> MvType (base s) -> Type where
  -- Any type is a sub-type of itself.
  ReflSub  : Subtype s t t
  -- Subtyping is a transitive relation.
  TransSub : {x,y,z : _ } -> Subtype s x y -> Subtype s y z -> Subtype s x z
  -- Subtyping can be preformed by an implicit conversion.
  Inject   : 
      (s : MvSchema)
   -> (x : MvType (base s))
   -> (y : MvType (base s))
   -> (z : MvBaseExpr (base s) x -> MvBaseExpr (base s) y)
   -> { auto p: (MkConversionDec x y z) `elem` conversions s = True }
   -> Subtype s x y
  -- Subtyping can be preformed by specifyin a subtype for
  -- an entity type.
  EntitySub : 
      (s : MvSchema) 
   -> (x : Nat) 
   -> (y : Nat)
   -> { auto p1: x `elem` types (base s) = True }
   -> { auto p2: y `elem` types (base s) = True }
   -> { auto p3: MkSubtypeDec x y `elem` subtypes (base s) = True } 
   -> Subtype s (EntityT (base s) x {p=p1}) (EntityT (base s) y {p=p2})

||| Helper function to preform a conversion from a subtype to it's supertype,
||| given evidence (Subtype s x y) that a term is a subtype of another term
||| according to the given schema.
convertTerm : 
      { s: MvSchema } 
   -> { x, y: _ }
   -> Subtype s x y 
   -> MvBaseExpr (base s) x 
   -> MvBaseExpr (base s) y
convertTerm ReflSub 
  = \t => t
convertTerm (TransSub t1 t2)  
  = convertTerm t2 . convertTerm t1
convertTerm (Inject s x y f)  
  = f
convertTerm (EntitySub s x y) 
  = InjectEntitySub (base s) x y

-- Examples

-- myType : Nat
-- myType = 0

-- schema : MvBaseSchema
-- schema = MkBaseSchema Nothing [myType] [] [MkEntityDec 0 myType, MkEntityDec 1 myType] () []

-- Note: For some reason, idris2 doesn't like it when I put variables in types -- it treats them like a hole.
-- exampleTerm : MvExpr (MkBaseSchema Nothing [myType] [] [MkEntityDec 0 myType, MkEntityDec 1 myType] () []) (MkBaseSchema Nothing [myType] [] [MkEntityDec 0 myType, MkEntityDec 1 myType] () [])
-- exampleTerm = EntityExp schema 1 0 

(+) : MvExpr s (FuncT IntT (FuncT IntT IntT))
(+) = FuncExp (\(IntExp x) => FuncExp $ \(IntExp y) => IntExp $ x + y)

main : IO ()
main = do
  let (IntExp x) = the (MvExpr (MkBaseSchema [] [] []) IntT) $
     evaluate $ AppExp (AppExp (+) (IntExp 2)) (IntExp 2)
  printLn x
