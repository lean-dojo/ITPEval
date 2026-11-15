-- Statement-only formalization of thousand-theorems corpus artifact
-- thousand-theorems__agda__Q208416, "Independence of the continuum hypothesis":
-- by first-order completeness, neither CH nor its negation is a semantic
-- consequence of the source ZFC theory. This file contains no proof.

{-# OPTIONS --safe #-}

module Q208416_independence_of_the_continuum_hypothesis where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 4 _and_
infixr 3 _or_
infix 2 _iff_

data Bottom : Set where

Not : {a : Level} -> Set a -> Set a
Not proposition =
  proposition -> Bottom

NotEqual :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  Set a
NotEqual left right =
  Not (left == right)

record _and_
  {a b : Level}
  (left : Set a)
  (right : Set b) :
  Set (a ⊔ b) where

  constructor conjunction
  field
    first : left
    second : right

data _or_
  {a b : Level}
  (left : Set a)
  (right : Set b) :
  Set (a ⊔ b) where

  left-disjunct : left -> left or right
  right-disjunct : right -> left or right

record _iff_
  {a b : Level}
  (left : Set a)
  (right : Set b) :
  Set (a ⊔ b) where

  constructor equivalence
  field
    forward : left -> right
    backward : right -> left

record Exists
  {a p : Level}
  (A : Set a)
  (property : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value : A
    evidence : property value

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc : {n : Nat} -> Fin n -> Fin (suc n)

Environment : Set -> Nat -> Set
Environment A n =
  Fin n -> A

extend :
  {A : Set} ->
  {n : Nat} ->
  Environment A n ->
  A ->
  Environment A (suc n)
extend environment new-value fzero =
  new-value
extend environment new-value (fsuc index) =
  environment index

extend-two :
  {A : Set} ->
  {n : Nat} ->
  Environment A n ->
  A ->
  A ->
  Environment A (suc (suc n))
extend-two environment first-value second-value =
  extend (extend environment first-value) second-value

data Term (free-variables : Nat) : Set where
  var-term : Fin free-variables -> Term free-variables
  empty-term : Term free-variables
  ordered-pair-term :
    Term free-variables ->
    Term free-variables ->
    Term free-variables
  omega-term : Term free-variables
  power-set-term : Term free-variables -> Term free-variables
  union-term : Term free-variables -> Term free-variables

data Formula (free-variables : Nat) : Set where
  falsum : Formula free-variables
  equal :
    Term free-variables ->
    Term free-variables ->
    Formula free-variables
  member :
    Term free-variables ->
    Term free-variables ->
    Formula free-variables
  implication :
    Formula free-variables ->
    Formula free-variables ->
    Formula free-variables
  universal :
    Formula (suc free-variables) ->
    Formula free-variables

record SetStructure : Set₁ where
  field
    Carrier : Set
    membership : Carrier -> Carrier -> Set
    empty-set : Carrier
    ordered-pair : Carrier -> Carrier -> Carrier
    omega : Carrier
    power-set : Carrier -> Carrier
    union-set : Carrier -> Carrier

open SetStructure

InterpretTerm :
  (structure : SetStructure) ->
  {n : Nat} ->
  Environment (Carrier structure) n ->
  Term n ->
  Carrier structure
InterpretTerm structure environment (var-term index) =
  environment index
InterpretTerm structure environment empty-term =
  empty-set structure
InterpretTerm structure environment (ordered-pair-term left right) =
  ordered-pair structure
    (InterpretTerm structure environment left)
    (InterpretTerm structure environment right)
InterpretTerm structure environment omega-term =
  omega structure
InterpretTerm structure environment (power-set-term set-term) =
  power-set structure
    (InterpretTerm structure environment set-term)
InterpretTerm structure environment (union-term family-term) =
  union-set structure
    (InterpretTerm structure environment family-term)

Satisfies :
  (structure : SetStructure) ->
  {n : Nat} ->
  Environment (Carrier structure) n ->
  Formula n ->
  Set
Satisfies structure environment falsum =
  Bottom
Satisfies structure environment (equal left right) =
  InterpretTerm structure environment left ==
  InterpretTerm structure environment right
Satisfies structure environment (member element set-term) =
  membership structure
    (InterpretTerm structure environment element)
    (InterpretTerm structure environment set-term)
Satisfies structure environment (implication antecedent consequent) =
  Satisfies structure environment antecedent ->
  Satisfies structure environment consequent
Satisfies structure environment (universal body) =
  (value : Carrier structure) ->
  Satisfies structure (extend environment value) body

Subset :
  (structure : SetStructure) ->
  Carrier structure ->
  Carrier structure ->
  Set
Subset structure left right =
  (element : Carrier structure) ->
  membership structure element left ->
  membership structure element right

Nonempty :
  (structure : SetStructure) ->
  Carrier structure ->
  Set
Nonempty structure set =
  NotEqual set (empty-set structure)

TransitiveSet :
  (structure : SetStructure) ->
  Carrier structure ->
  Set
TransitiveSet structure set =
  (element : Carrier structure) ->
  membership structure element set ->
  Subset structure element set

MembershipTrichotomous :
  (structure : SetStructure) ->
  Carrier structure ->
  Set
MembershipTrichotomous structure set =
  (left right : Carrier structure) ->
  membership structure left set ->
  membership structure right set ->
  ((left == right) or membership structure left right) or
  membership structure right left

MembershipWellFounded :
  (structure : SetStructure) ->
  Carrier structure ->
  Set
MembershipWellFounded structure set =
  (subset : Carrier structure) ->
  Subset structure subset set ->
  Nonempty structure subset ->
  Exists (Carrier structure)
    (\ least ->
      membership structure least subset and
      ((other : Carrier structure) ->
       membership structure other subset ->
       Not (membership structure other least)))

Ordinal :
  (structure : SetStructure) ->
  Carrier structure ->
  Set
Ordinal structure set =
  (MembershipTrichotomous structure set and
   MembershipWellFounded structure set) and
  TransitiveSet structure set

LimitProperty :
  (structure : SetStructure) ->
  Carrier structure ->
  Set
LimitProperty structure set =
  membership structure (empty-set structure) set and
  ((element : Carrier structure) ->
   membership structure element set ->
   Exists (Carrier structure)
     (\ successor ->
       membership structure successor set and
       membership structure element successor))

ChainIn :
  (structure : SetStructure) ->
  Carrier structure ->
  Carrier structure ->
  Set
ChainIn structure chain ambient =
  Subset structure chain ambient and
  ((left right : Carrier structure) ->
   membership structure left chain ->
   membership structure right chain ->
   Subset structure left right or
   Subset structure right left)

FunctionalGraph :
  (structure : SetStructure) ->
  Carrier structure ->
  Set
FunctionalGraph structure graph =
  (input-one input-two output-one output-two : Carrier structure) ->
  membership structure
    (ordered-pair structure input-one output-one) graph ->
  membership structure
    (ordered-pair structure input-two output-two) graph ->
  input-one == input-two ->
  output-one == output-two

TotalFromTo :
  (structure : SetStructure) ->
  Carrier structure ->
  Carrier structure ->
  Carrier structure ->
  Set
TotalFromTo structure graph domain codomain =
  (input : Carrier structure) ->
  membership structure input domain ->
  Exists (Carrier structure)
    (\ output ->
      membership structure output codomain and
      membership structure
        (ordered-pair structure input output) graph)

SurjectiveFromTo :
  (structure : SetStructure) ->
  Carrier structure ->
  Carrier structure ->
  Carrier structure ->
  Set
SurjectiveFromTo structure graph domain codomain =
  (output : Carrier structure) ->
  membership structure output codomain ->
  Exists (Carrier structure)
    (\ input ->
      membership structure input domain and
      membership structure
        (ordered-pair structure input output) graph)

AtMost :
  (structure : SetStructure) ->
  Carrier structure ->
  Carrier structure ->
  Set
AtMost structure smaller larger =
  Exists (Carrier structure)
    (\ domain ->
      Subset structure domain larger and
      Exists (Carrier structure)
        (\ graph ->
          FunctionalGraph structure graph and
          (TotalFromTo structure graph domain smaller and
           SurjectiveFromTo structure graph domain smaller)))

ContinuumHypothesis :
  (structure : SetStructure) ->
  Set
ContinuumHypothesis structure =
  (ordinal : Carrier structure) ->
  Ordinal structure ordinal ->
  AtMost structure ordinal (omega structure) or
  AtMost structure (power-set structure (omega structure)) ordinal

record ModelsZFC (structure : SetStructure) : Set where
  field
    empty-set-axiom :
      (element : Carrier structure) ->
      Not (membership structure element (empty-set structure))

    ordered-pair-axiom :
      (left-one right-one left-two right-two : Carrier structure) ->
      (ordered-pair structure left-one right-one ==
       ordered-pair structure left-two right-two) iff
      ((left-one == left-two) and (right-one == right-two))

    extensionality :
      (left right : Carrier structure) ->
      ((element : Carrier structure) ->
       membership structure element left iff
       membership structure element right) ->
      left == right

    strong-collection :
      (parameter-count : Nat) ->
      (formula : Formula (suc (suc parameter-count))) ->
      (parameters : Environment (Carrier structure) parameter-count) ->
      (source-set : Carrier structure) ->
      ((input : Carrier structure) ->
       membership structure input source-set ->
       Exists (Carrier structure)
         (\ output ->
           Satisfies structure
             (extend-two parameters input output)
             formula)) ->
      Exists (Carrier structure)
        (\ collection ->
          ((input : Carrier structure) ->
           membership structure input source-set ->
           Exists (Carrier structure)
             (\ output ->
               membership structure output collection and
               Satisfies structure
                 (extend-two parameters input output)
                 formula)) and
          ((output : Carrier structure) ->
           membership structure output collection ->
           Exists (Carrier structure)
             (\ input ->
               membership structure input source-set and
               Satisfies structure
                 (extend-two parameters input output)
                 formula)))

    union-axiom :
      (family element : Carrier structure) ->
      membership structure element (union-set structure family) iff
      Exists (Carrier structure)
        (\ member-set ->
          membership structure member-set family and
          membership structure element member-set)

    power-set-axiom :
      (set subset : Carrier structure) ->
      membership structure subset (power-set structure set) iff
      Subset structure subset set

    infinity-limit :
      LimitProperty structure (omega structure)

    infinity-ordinal :
      Exists (Carrier structure)
        (\ ordinal ->
          Ordinal structure ordinal and
          (omega structure == ordinal))

    infinity-least :
      (ordinal : Carrier structure) ->
      Ordinal structure ordinal ->
      LimitProperty structure ordinal ->
      Subset structure (omega structure) ordinal

    regularity :
      (set : Carrier structure) ->
      Nonempty structure set ->
      Exists (Carrier structure)
        (\ least ->
          membership structure least set and
          ((other : Carrier structure) ->
           membership structure other set ->
           Not (membership structure other least)))

    zorns-lemma :
      (set : Carrier structure) ->
      Nonempty structure set ->
      ((chain : Carrier structure) ->
       ChainIn structure chain set ->
       membership structure (union-set structure chain) set) ->
      Exists (Carrier structure)
        (\ maximal ->
          membership structure maximal set and
          ((other : Carrier structure) ->
           membership structure other set ->
           Subset structure maximal other ->
           maximal == other))

ZFC-Entails :
  (property : (structure : SetStructure) -> Set) ->
  Set₁
ZFC-Entails property =
  (structure : SetStructure) ->
  ModelsZFC structure ->
  property structure

independence-of-the-continuum-hypothesis : Set₁
independence-of-the-continuum-hypothesis =
  Not (ZFC-Entails ContinuumHypothesis) and
  Not
    (ZFC-Entails
      (\ structure ->
        Not (ContinuumHypothesis structure)))
