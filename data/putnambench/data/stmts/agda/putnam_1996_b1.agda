-- Statement-only formalization of PutnamBench corpus artifact putnam_1996_b1:
-- the number of minimal finite subsets of {1,...,n} that contain their own
-- cardinality is the nth Fibonacci number. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _<=N_
infixr 3 _and_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

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

record HasCardinality
  {A : Set}
  (member : A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      member (enumerate index)
    enumeration-complete :
      (item : A) ->
      member item ->
      Exists (Fin cardinality)
        (\ index -> item == enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

record FiniteNatSet : Set where
  constructor finiteNatSet
  field
    membership      : Nat -> Bool
    size            : Nat
    has-cardinality :
      HasCardinality
        (\ n -> membership n == true)
        size

open FiniteNatSet

SameFiniteNatSet :
  FiniteNatSet ->
  FiniteNatSet ->
  Set
SameFiniteNatSet left right =
  (n : Nat) ->
  membership left n == membership right n

SubsetOf :
  FiniteNatSet ->
  FiniteNatSet ->
  Set
SubsetOf left right =
  (n : Nat) ->
  membership left n == true ->
  membership right n == true

StrictSubset :
  FiniteNatSet ->
  FiniteNatSet ->
  Set
StrictSubset left right =
  SubsetOf left right
  and
  Not (SubsetOf right left)

one : Nat
one =
  suc zero

InInterval :
  Nat ->
  Nat ->
  Set
InInterval upper n =
  one <=N n
  and
  n <=N upper

ContainedInInterval :
  Nat ->
  FiniteNatSet ->
  Set
ContainedInInterval upper set =
  (n : Nat) ->
  membership set n == true ->
  InInterval upper n

Selfish :
  FiniteNatSet ->
  Set
Selfish set =
  membership set (size set) == true

MinimalSelfishWithin :
  Nat ->
  FiniteNatSet ->
  Set
MinimalSelfishWithin upper set =
  ContainedInInterval upper set
  and
  Selfish set
  and
  ((subset : FiniteNatSet) ->
    StrictSubset subset set ->
    Not (Selfish subset))

record HasExtensionalCardinality
  {A : Set}
  (member : A -> Set)
  (equivalent : A -> A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      member (enumerate index)
    enumeration-complete :
      (item : A) ->
      member item ->
      Exists (Fin cardinality)
        (\ index -> equivalent item (enumerate index))
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      equivalent (enumerate left-index) (enumerate right-index) ->
      left-index == right-index

fibonacci : Nat -> Nat
fibonacci zero =
  zero
fibonacci (suc zero) =
  one
fibonacci (suc (suc n)) =
  fibonacci n + fibonacci (suc n)

putnam-1996-b1-solution :
  Nat ->
  Nat
putnam-1996-b1-solution =
  fibonacci

putnam-1996-b1 : Set
putnam-1996-b1 =
  (n : Nat) ->
  one <=N n ->
  HasExtensionalCardinality
    (MinimalSelfishWithin n)
    SameFiniteNatSet
    (putnam-1996-b1-solution n)
