-- Statement-only formalization of Hundred Theorems artifact 024, "The
-- Undecidability of the Continuum Hypothesis": every countable transitive set
-- model of ZF has a proper countable transitive ZF extension with the same
-- ordinals, and source-model AC yields ZFC in the extension. This file
-- contains no proof.

module Main where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; suc)

infixr 3 _and_
infixr 2 _or_
infix 1 _iff_

data Bottom : Set where

Not : {a : Level} -> Set a -> Set a
Not A = A -> Bottom

NotEqual : {a : Level} {A : Set a} -> A -> A -> Set a
NotEqual x y = Not (x == y)

record Top : Set where
  constructor top

record _and_ {a b : Level} (A : Set a) (B : Set b) :
  Set (a ⊔ b) where
  constructor both
  field
    first  : A
    second : B

data _or_ {a b : Level} (A : Set a) (B : Set b) :
  Set (a ⊔ b) where
  left  : A -> A or B
  right : B -> A or B

record _iff_ {a b : Level} (A : Set a) (B : Set b) :
  Set (a ⊔ b) where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists {a p : Level} (A : Set a) (P : A -> Set p) :
  Set (a ⊔ p) where
  constructor witness
  field
    value    : A
    property : P value

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

-- This structure becomes the ambient Isabelle/ZF universe only through the
-- ZFUniverse record below, which requires the complete ZF theory.
record MembershipStructure : Set₁ where
  field
    Carrier    : Set
    membership : Carrier -> Carrier -> Set

open MembershipStructure

UniversalDomain :
  (S : MembershipStructure) ->
  Carrier S ->
  Set
UniversalDomain S x = Top

record InDomain
  (S : MembershipStructure)
  (D : Carrier S -> Set) :
  Set where

  constructor element
  field
    object    : Carrier S
    in-domain : D object

open InDomain

-- This is the full first-order language used by Isabelle/ZF: atomic equality
-- and membership, Sheffer NAND, and universal quantification. The index gives
-- the exact finite environment length. Thus the syntax ranges over every
-- formula with every arbitrary finite tuple of parameters; it is the
-- well-scoped de Bruijn presentation of Isabelle's formula/environment lists.
data Formula (free-variables : Nat) : Set where
  Equal  :
    Fin free-variables ->
    Fin free-variables ->
    Formula free-variables
  Member :
    Fin free-variables ->
    Fin free-variables ->
    Formula free-variables
  Nand   :
    Formula free-variables ->
    Formula free-variables ->
    Formula free-variables
  Forall :
    Formula (suc free-variables) ->
    Formula free-variables

Assignment :
  (S : MembershipStructure) ->
  (D : Carrier S -> Set) ->
  Nat ->
  Set
Assignment S D n =
  Fin n -> InDomain S D

extend :
  {A : Set} ->
  {n : Nat} ->
  (Fin n -> A) ->
  A ->
  Fin (suc n) ->
  A
extend assignment new-value fzero =
  new-value
extend assignment new-value (fsuc index) =
  assignment index

-- Recursive Tarskian satisfaction for precisely that formula language.
-- In particular, no excluded-middle or decidability field is assumed.
Satisfies :
  (S : MembershipStructure) ->
  (D : Carrier S -> Set) ->
  {free-variables : Nat} ->
  Formula free-variables ->
  Assignment S D free-variables ->
  Set
Satisfies S D (Equal i j) assignment =
  object (assignment i) == object (assignment j)
Satisfies S D (Member i j) assignment =
  membership S (object (assignment i)) (object (assignment j))
Satisfies S D (Nand left-formula right-formula) assignment =
  Not
    (Satisfies S D left-formula assignment and
     Satisfies S D right-formula assignment)
Satisfies S D (Forall formula) assignment =
  (x : InDomain S D) ->
  Satisfies S D formula (extend assignment x)

record ExistsUniqueIn
  (S : MembershipStructure)
  (D : Carrier S -> Set)
  (P : InDomain S D -> Set) :
  Set where

  constructor unique-witness
  field
    unique-value    : InDomain S D
    unique-property : P unique-value
    uniqueness      :
      (other : InDomain S D) ->
      P other ->
      object other == object unique-value

SubsetObject :
  (S : MembershipStructure) ->
  Carrier S ->
  Carrier S ->
  Set
SubsetObject S a b =
  (x : Carrier S) ->
  membership S x a ->
  membership S x b

Transset :
  (S : MembershipStructure) ->
  Carrier S ->
  Set
Transset S a =
  (x y : Carrier S) ->
  membership S x y ->
  membership S y a ->
  membership S x a

SameMembersIn :
  (S : MembershipStructure) ->
  (D : Carrier S -> Set) ->
  Carrier S ->
  Carrier S ->
  Set
SameMembersIn S D a b =
  (x : InDomain S D) ->
  (membership S (object x) a iff
   membership S (object x) b)

IsEmptyIn :
  (S : MembershipStructure) ->
  (D : Carrier S -> Set) ->
  Carrier S ->
  Set
IsEmptyIn S D empty =
  (x : InDomain S D) ->
  Not (membership S (object x) empty)

IsInhabitedIn :
  (S : MembershipStructure) ->
  (D : Carrier S -> Set) ->
  Carrier S ->
  Set
IsInhabitedIn S D a =
  Exists (InDomain S D)
    (\ x -> membership S (object x) a)

SubsetIn :
  (S : MembershipStructure) ->
  (D : Carrier S -> Set) ->
  Carrier S ->
  Carrier S ->
  Set
SubsetIn S D a b =
  (x : InDomain S D) ->
  membership S (object x) a ->
  membership S (object x) b

IsPairIn :
  (S : MembershipStructure) ->
  (D : Carrier S -> Set) ->
  Carrier S ->
  Carrier S ->
  Carrier S ->
  Set
IsPairIn S D a b pair =
  (x : InDomain S D) ->
  (membership S (object x) pair iff
   (object x == a or object x == b))

IsUnionIn :
  (S : MembershipStructure) ->
  (D : Carrier S -> Set) ->
  Carrier S ->
  Carrier S ->
  Set
IsUnionIn S D family union =
  (x : InDomain S D) ->
  (membership S (object x) union iff
   Exists (InDomain S D)
     (\ member ->
       membership S (object member) family and
       membership S (object x) (object member)))

IsPowerSetIn :
  (S : MembershipStructure) ->
  (D : Carrier S -> Set) ->
  Carrier S ->
  Carrier S ->
  Set
IsPowerSetIn S D a power =
  (x : InDomain S D) ->
  (membership S (object x) power iff
   SubsetIn S D (object x) a)

IsSuccessorIn :
  (S : MembershipStructure) ->
  (D : Carrier S -> Set) ->
  Carrier S ->
  Carrier S ->
  Set
IsSuccessorIn S D a successor =
  (x : InDomain S D) ->
  (membership S (object x) successor iff
   (membership S (object x) a or object x == a))

IsInductiveIn :
  (S : MembershipStructure) ->
  (D : Carrier S -> Set) ->
  Carrier S ->
  Set
IsInductiveIn S D inductive-set =
  Exists (InDomain S D)
    (\ empty ->
      IsEmptyIn S D (object empty) and
      membership S (object empty) inductive-set) and
  ((x : InDomain S D) ->
    membership S (object x) inductive-set ->
    Exists (InDomain S D)
      (\ successor ->
        IsSuccessorIn S D (object x) (object successor) and
        membership S (object successor) inductive-set))

IsOmega :
  (S : MembershipStructure) ->
  Carrier S ->
  Set
IsOmega S omega =
  IsInductiveIn S (UniversalDomain S) omega and
  ((inductive-set : Carrier S) ->
    IsInductiveIn S (UniversalDomain S) inductive-set ->
    SubsetObject S omega inductive-set)

FunctionalFormulaOn :
  (S : MembershipStructure) ->
  (D : Carrier S -> Set) ->
  {parameter-count : Nat} ->
  Formula (suc (suc parameter-count)) ->
  Assignment S D parameter-count ->
  Carrier S ->
  Set
FunctionalFormulaOn S D formula parameters domain =
  (x : InDomain S D) ->
  membership S (object x) domain ->
  ExistsUniqueIn S D
    (\ y ->
      Satisfies S D formula
        (extend (extend parameters x) y))

-- A model satisfies ZF exactly when it satisfies all eight axioms, with
-- Separation and Replacement ranging over the complete syntax above and all
-- finite parameter environments.
record SatisfiesZF
  (S : MembershipStructure)
  (D : Carrier S -> Set) :
  Set where

  field
    extensionality :
      (a b : InDomain S D) ->
      SameMembersIn S D (object a) (object b) ->
      object a == object b

    empty-set :
      Exists (InDomain S D)
        (\ empty -> IsEmptyIn S D (object empty))

    pairing :
      (a b : InDomain S D) ->
      Exists (InDomain S D)
        (\ pair ->
          IsPairIn S D (object a) (object b) (object pair))

    union :
      (a : InDomain S D) ->
      Exists (InDomain S D)
        (\ union-set ->
          IsUnionIn S D (object a) (object union-set))

    power-set :
      (a : InDomain S D) ->
      Exists (InDomain S D)
        (\ power ->
          IsPowerSetIn S D (object a) (object power))

    infinity :
      Exists (InDomain S D)
        (\ inductive-set ->
          IsInductiveIn S D (object inductive-set))

    separation :
      (parameter-count : Nat) ->
      (formula : Formula (suc parameter-count)) ->
      (parameters : Assignment S D parameter-count) ->
      (a : InDomain S D) ->
      Exists (InDomain S D)
        (\ subset ->
          (x : InDomain S D) ->
          (membership S (object x) (object subset) iff
           (membership S (object x) (object a) and
            Satisfies S D formula (extend parameters x))))

    -- Variable zero is the value, variable one the argument, and the
    -- remaining variables are the arbitrary parameter tuple.
    replacement :
      (parameter-count : Nat) ->
      (formula : Formula (suc (suc parameter-count))) ->
      (parameters : Assignment S D parameter-count) ->
      (a : InDomain S D) ->
      FunctionalFormulaOn S D formula parameters (object a) ->
      Exists (InDomain S D)
        (\ image ->
          (y : InDomain S D) ->
          (membership S (object y) (object image) iff
           Exists (InDomain S D)
             (\ x ->
               membership S (object x) (object a) and
               Satisfies S D formula
                 (extend (extend parameters x) y))))

    foundation :
      (a : InDomain S D) ->
      IsInhabitedIn S D (object a) ->
      Exists (InDomain S D)
        (\ least ->
          membership S (object least) (object a) and
          ((x : InDomain S D) ->
            membership S (object x) (object least) ->
            Not (membership S (object x) (object a))))

-- A ZFUniverse represents the fixed ambient Isabelle/ZF set universe. Thus
-- every object quantified below, including N and every ordinal, is an ambient
-- set rather than an element of an unconstrained relational structure.
record ZFUniverse : Set₁ where
  field
    ambient                  : MembershipStructure
    ambient-satisfies-ZF     :
      SatisfiesZF ambient (UniversalDomain ambient)
    natural-numbers          : Carrier ambient
    natural-numbers-is-omega : IsOmega ambient natural-numbers

open ZFUniverse

SetObject : ZFUniverse -> Set
SetObject U =
  Carrier (ambient U)

Belongs :
  (U : ZFUniverse) ->
  SetObject U ->
  SetObject U ->
  Set
Belongs U =
  membership (ambient U)

ModelDomain :
  (U : ZFUniverse) ->
  SetObject U ->
  SetObject U ->
  Set
ModelDomain U M x =
  Belongs U x M

IsSingleton :
  (S : MembershipStructure) ->
  Carrier S ->
  Carrier S ->
  Set
IsSingleton S x singleton =
  (z : InDomain S (UniversalDomain S)) ->
  (membership S (object z) singleton iff object z == x)

-- Isabelle/ZF functions and bijections are ambient sets of Kuratowski ordered
-- pairs. This definition says that pair-code is {{x},{x,y}}.
IsOrderedPair :
  (S : MembershipStructure) ->
  Carrier S ->
  Carrier S ->
  Carrier S ->
  Set
IsOrderedPair S x y pair-code =
  Exists (Carrier S)
    (\ singleton ->
      IsSingleton S x singleton and
      Exists (Carrier S)
        (\ unordered-pair ->
          IsPairIn S (UniversalDomain S) x y unordered-pair and
          IsPairIn S (UniversalDomain S)
            singleton unordered-pair pair-code))

GraphRelates :
  (S : MembershipStructure) ->
  Carrier S ->
  Carrier S ->
  Carrier S ->
  Set
GraphRelates S graph x y =
  Exists (Carrier S)
    (\ pair-code ->
      membership S pair-code graph and
      IsOrderedPair S x y pair-code)

record IsSetCodedBijection
  (S : MembershipStructure)
  (graph domain codomain : Carrier S) :
  Set where

  field
    graph-between :
      (pair-code : Carrier S) ->
      membership S pair-code graph ->
      Exists (InDomain S (\ x -> membership S x domain))
        (\ x ->
          Exists (InDomain S (\ y -> membership S y codomain))
            (\ y ->
              IsOrderedPair S
                (object x) (object y) pair-code))

    total-and-functional :
      (x : InDomain S (\ z -> membership S z domain)) ->
      ExistsUniqueIn S (\ y -> membership S y codomain)
        (\ y -> GraphRelates S graph (object x) (object y))

    injective :
      (x-one x-two : InDomain S (\ z -> membership S z domain)) ->
      (y : InDomain S (\ z -> membership S z codomain)) ->
      GraphRelates S graph (object x-one) (object y) ->
      GraphRelates S graph (object x-two) (object y) ->
      object x-one == object x-two

    surjective :
      (y : InDomain S (\ z -> membership S z codomain)) ->
      Exists (InDomain S (\ x -> membership S x domain))
        (\ x -> GraphRelates S graph (object x) (object y))

Equinumerous :
  (S : MembershipStructure) ->
  Carrier S ->
  Carrier S ->
  Set
Equinumerous S a b =
  Exists (Carrier S)
    (\ graph -> IsSetCodedBijection S graph a b)

Countable :
  (U : ZFUniverse) ->
  SetObject U ->
  Set
Countable U M =
  Equinumerous (ambient U) M (natural-numbers U)

NonemptyMembersIn :
  (S : MembershipStructure) ->
  (D : Carrier S -> Set) ->
  Carrier S ->
  Set
NonemptyMembersIn S D family =
  (a : InDomain S D) ->
  membership S (object a) family ->
  Exists (InDomain S D)
    (\ x -> membership S (object x) (object a))

PairwiseDisjointIn :
  (S : MembershipStructure) ->
  (D : Carrier S -> Set) ->
  Carrier S ->
  Set
PairwiseDisjointIn S D family =
  (a b : InDomain S D) ->
  membership S (object a) family ->
  membership S (object b) family ->
  NotEqual (object a) (object b) ->
  (x : InDomain S D) ->
  membership S (object x) (object a) ->
  Not (membership S (object x) (object b))

IsChoiceSetIn :
  (S : MembershipStructure) ->
  (D : Carrier S -> Set) ->
  Carrier S ->
  Carrier S ->
  Set
IsChoiceSetIn S D family choice =
  (a : InDomain S D) ->
  membership S (object a) family ->
  ExistsUniqueIn S D
    (\ selected ->
      membership S (object selected) (object a) and
      membership S (object selected) choice)

ChoiceAxiom :
  (S : MembershipStructure) ->
  (D : Carrier S -> Set) ->
  Set
ChoiceAxiom S D =
  (family : InDomain S D) ->
  NonemptyMembersIn S D (object family) ->
  PairwiseDisjointIn S D (object family) ->
  Exists (InDomain S D)
    (\ choice ->
      IsChoiceSetIn S D (object family) (object choice))

SatisfiesZFC :
  (S : MembershipStructure) ->
  (D : Carrier S -> Set) ->
  Set
SatisfiesZFC S D =
  SatisfiesZF S D and ChoiceAxiom S D

-- Isabelle/ZF defines an ordinal as a transitive set whose elements are
-- transitive sets. The surrounding ZF universe supplies Foundation.
IsOrdinal :
  (S : MembershipStructure) ->
  Carrier S ->
  Set
IsOrdinal S ordinal =
  Transset S ordinal and
  ((member : Carrier S) ->
    membership S member ordinal ->
    Transset S member)

SameOrdinals :
  (U : ZFUniverse) ->
  SetObject U ->
  SetObject U ->
  Set
SameOrdinals U M N =
  (ordinal : SetObject U) ->
  IsOrdinal (ambient U) ordinal ->
  (Belongs U ordinal M iff Belongs U ordinal N)

the-undecidability-of-the-continuum-hypothesis : Set₁
the-undecidability-of-the-continuum-hypothesis =
  (U : ZFUniverse) ->
  (M : SetObject U) ->
  Countable U M ->
  Transset (ambient U) M ->
  SatisfiesZF (ambient U) (ModelDomain U M) ->
  Exists (SetObject U)
    (\ N ->
      SubsetObject (ambient U) M N and
      Countable U N and
      Transset (ambient U) N and
      SatisfiesZF (ambient U) (ModelDomain U N) and
      NotEqual M N and
      SameOrdinals U M N and
      (ChoiceAxiom (ambient U) (ModelDomain U M) ->
       SatisfiesZFC (ambient U) (ModelDomain U N)))
