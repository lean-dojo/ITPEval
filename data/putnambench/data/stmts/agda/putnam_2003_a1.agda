-- Statement-only formalization of PutnamBench corpus artifact putnam_2003_a1
-- (putnambench__agda__putnam_2003_a1): every positive integer n has exactly n
-- nondecreasing positive-integer compositions whose last part is at most one
-- greater than the first. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2003A1 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<= :
    {n : Nat} ->
    zero <= n
  suc<=suc :
    {m n : Nat} ->
    m <= n ->
    suc m <= suc n

data Fin : Nat -> Set where
  fzero :
    {n : Nat} ->
    Fin (suc n)
  fsuc :
    {n : Nat} ->
    Fin n ->
    Fin (suc n)

record Exists
  (A : Set)
  (P : A -> Set) :
  Set where

  constructor witness
  field
    value    : A
    property : P value

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

data Positive : Nat -> Set where
  positive :
    {n : Nat} ->
    Positive (suc n)

data NonEmpty {A : Set} : List A -> Set where
  nonempty :
    {x : A} {xs : List A} ->
    NonEmpty (x ∷ xs)

data All {A : Set} (P : A -> Set) : List A -> Set where
  all-empty :
    All P []
  all-cons :
    {x : A} {xs : List A} ->
    P x ->
    All P xs ->
    All P (x ∷ xs)

data NonDecreasing : List Nat -> Set where
  nondecreasing-empty :
    NonDecreasing []
  nondecreasing-singleton :
    {x : Nat} ->
    NonDecreasing (x ∷ [])
  nondecreasing-cons :
    {x y : Nat} {xs : List Nat} ->
    x <= y ->
    NonDecreasing (y ∷ xs) ->
    NonDecreasing (x ∷ y ∷ xs)

sum : List Nat -> Nat
sum [] =
  zero
sum (x ∷ xs) =
  x + sum xs

head : List Nat -> Nat
head [] =
  zero
head (x ∷ xs) =
  x

last : List Nat -> Nat
last [] =
  zero
last (x ∷ []) =
  x
last (x ∷ y ∷ xs) =
  last (y ∷ xs)

record IsPutnamComposition
  (n : Nat)
  (parts : List Nat) :
  Set where

  field
    positive-length :
      NonEmpty parts
    positive-parts :
      All Positive parts
    ordered-parts :
      NonDecreasing parts
    correct-sum :
      sum parts == n
    endpoint-bound :
      last parts <= head parts + suc zero

putnam-2003-a1 : Set
putnam-2003-a1 =
  (n : Nat) ->
  Positive n ->
  HasCardinality (IsPutnamComposition n) n
