-- Statement-only formalization of PutnamBench corpus artifact putnam_1978_a1:
-- every 20-element subset of the integers 1, 4, 7, ..., 100 contains two
-- distinct elements whose sum is 104. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=_ _!=_
infixr 3 _and_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

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

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=  : {m n : Nat} -> m <= n -> suc m <= suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

NatSubset : Set1
NatSubset =
  Nat -> Set

SubsetOf : NatSubset -> NatSubset -> Set
SubsetOf A B =
  (x : Nat) -> A x -> B x

record SameSubset (A B : NatSubset) : Set where
  field
    forward  : SubsetOf A B
    backward : SubsetOf B A

record HasCardinality
  (S : NatSubset)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      Nat
    enumerated-member :
      (index : Fin cardinality) ->
      S (enumerate index)
    enumeration-complete :
      (number : Nat) ->
      S number ->
      Exists (Fin cardinality)
        (\ index -> number == enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

PutnamProgression : NatSubset
PutnamProgression k =
  Exists Nat
    (\ j ->
      j <= 33
      and
      k == 3 * j + 1)

putnam-1978-a1 : Set1
putnam-1978-a1 =
  (S T : NatSubset) ->
  SameSubset S PutnamProgression ->
  (SubsetOf T S and HasCardinality T 20) ->
  Exists Nat
    (\ m ->
      T m
      and
      Exists Nat
        (\ n ->
          T n
          and
          m != n
          and
          m + n == 104))
