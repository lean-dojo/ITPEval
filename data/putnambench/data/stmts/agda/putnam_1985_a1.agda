-- Statement-only formalization of PutnamBench corpus artifact putnam_1985_a1:
-- the ordered triples of sets of natural numbers whose union is {1,...,10}
-- and whose triple intersection is empty number 2^10 * 3^10. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _<=N_
infixr 3 _and_
infixr 2 _or_
infix 1 _iff_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record _iff_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

three : Nat
three =
  suc two

four : Nat
four =
  suc three

five : Nat
five =
  suc four

six : Nat
six =
  suc five

seven : Nat
seven =
  suc six

eight : Nat
eight =
  suc seven

nine : Nat
nine =
  suc eight

ten : Nat
ten =
  suc nine

power : Nat -> Nat -> Nat
power base zero =
  one
power base (suc exponent) =
  base * power base exponent

SetPredicate : Set1
SetPredicate =
  Nat -> Set

record OrderedTriple : Set1 where
  constructor triple
  field
    first-set  : SetPredicate
    second-set : SetPredicate
    third-set  : SetPredicate

open OrderedTriple

unionMember : OrderedTriple -> Nat -> Set
unionMember sets n =
  first-set sets n or
  second-set sets n or
  third-set sets n

intersectionMember : OrderedTriple -> Nat -> Set
intersectionMember sets n =
  first-set sets n and
  second-set sets n and
  third-set sets n

inOneThroughTen : Nat -> Set
inOneThroughTen n =
  one <=N n and n <=N ten

SameSet : SetPredicate -> SetPredicate -> Set
SameSet left-set right-set =
  (n : Nat) ->
  _iff_ (left-set n) (right-set n)

SameTriple : OrderedTriple -> OrderedTriple -> Set
SameTriple left-triple right-triple =
  SameSet
    (first-set left-triple)
    (first-set right-triple)
  and
  SameSet
    (second-set left-triple)
    (second-set right-triple)
  and
  SameSet
    (third-set left-triple)
    (third-set right-triple)

ValidTriple : OrderedTriple -> Set
ValidTriple sets =
  SameSet (unionMember sets) inOneThroughTen
  and
  ((n : Nat) -> Not (intersectionMember sets n))

record HasValidExtensionalCardinality
  (cardinality : Nat) :
  Set1 where

  field
    enumerate :
      Fin cardinality ->
      OrderedTriple

    enumerated-valid :
      (index : Fin cardinality) ->
      ValidTriple (enumerate index)

    enumeration-complete :
      (sets : OrderedTriple) ->
      ValidTriple sets ->
      Exists
        (Fin cardinality)
        (\ index -> SameTriple sets (enumerate index))

    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      SameTriple
        (enumerate left-index)
        (enumerate right-index) ->
      left-index == right-index

solution-a solution-b solution-c solution-d : Nat
solution-a =
  ten
solution-b =
  ten
solution-c =
  zero
solution-d =
  zero

solution : Nat
solution =
  power two solution-a *
  power three solution-b *
  power five solution-c *
  power seven solution-d

putnam-1985-a1 : Set1
putnam-1985-a1 =
  HasValidExtensionalCardinality solution
