-- Statement-only formalization of PutnamBench corpus artifact putnam_1966_b4:
-- every set of m*n+1 positive natural numbers contains either an m+1 element
-- divisibility antichain or an n+1 element divisibility chain. This file
-- contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _!=_ _<_ _divides_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc  : {m n : Nat} -> m < n -> suc m < suc n

record _divides_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient == dividend

Subset : Set
Subset = Nat -> Bool

SubsetOf : Subset -> Subset -> Set
SubsetOf T S =
  (x : Nat) ->
  T x == true ->
  S x == true

record HasCardinality (S : Subset) (count : Nat) : Set where
  field
    enumerate :
      Fin count ->
      Nat

    enumerated-member :
      (index : Fin count) ->
      S (enumerate index) == true

    enumeration-complete :
      (x : Nat) ->
      S x == true ->
      Exists (Fin count)
        (\ index -> enumerate index == x)

    enumeration-injective :
      (left-index right-index : Fin count) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

putnam-1966-b4 : Set
putnam-1966-b4 =
  (m n : Nat) ->
  (S : Subset) ->
  HasCardinality S (suc (m * n)) ->
  ((i : Nat) ->
    S i == true ->
    zero < i) ->
  Exists Subset
    (\ T ->
      SubsetOf T S
      and
      ((HasCardinality T (suc m)
        and
        ((j i : Nat) ->
          T j == true ->
          T i == true ->
          i != j ->
          Not (j divides i)))
      or
      (HasCardinality T (suc n)
        and
        ((j i : Nat) ->
          T j == true ->
          T i == true ->
          j < i ->
          j divides i))))
