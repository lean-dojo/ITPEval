-- Statement-only formalization of "The Partition Theorem (Euler)" from Hundred Theorems item 045.
-- For every natural number, it equates the finite numbers of partitions into distinct positive
-- parts and partitions into odd positive parts. This file contains no proof.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _==_ _<=_ _<_

data _==_ {A : Set} (x : A) : A -> Set where
  refl : x == x

data List (A : Set) : Set where
  nil : List A
  cons : A -> List A -> List A

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc : {n : Nat} -> Fin n -> Fin (suc n)

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n = suc m <= n

Positive : Nat -> Set
Positive n = suc zero <= n

data Odd : Nat -> Set where
  one-is-odd : Odd (suc zero)
  plus-two-is-odd : {n : Nat} -> Odd n -> Odd (suc (suc n))

data All {A : Set} (P : A -> Set) : List A -> Set where
  all-nil : All P nil
  all-cons :
    {x : A} {xs : List A} ->
    P x ->
    All P xs ->
    All P (cons x xs)

data NonIncreasing : List Nat -> Set where
  nonincreasing-nil : NonIncreasing nil
  nonincreasing-single :
    {x : Nat} ->
    NonIncreasing (cons x nil)
  nonincreasing-cons :
    {x y : Nat} {xs : List Nat} ->
    y <= x ->
    NonIncreasing (cons y xs) ->
    NonIncreasing (cons x (cons y xs))

data StrictlyDecreasing : List Nat -> Set where
  strictly-decreasing-nil : StrictlyDecreasing nil
  strictly-decreasing-single :
    {x : Nat} ->
    StrictlyDecreasing (cons x nil)
  strictly-decreasing-cons :
    {x y : Nat} {xs : List Nat} ->
    y < x ->
    StrictlyDecreasing (cons y xs) ->
    StrictlyDecreasing (cons x (cons y xs))

sum : List Nat -> Nat
sum nil = zero
sum (cons x xs) = x + sum xs

record IsPartition (n : Nat) (parts : List Nat) : Set where
  field
    positive-parts : All Positive parts
    canonical-order : NonIncreasing parts
    correct-sum : sum parts == n

record IsDistinctPartition (n : Nat) (parts : List Nat) : Set where
  field
    distinct-partition : IsPartition n parts
    distinct-parts : StrictlyDecreasing parts

record IsOddPartition (n : Nat) (parts : List Nat) : Set where
  field
    odd-partition : IsPartition n parts
    odd-parts : All Odd parts

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value : A
    evidence : P value

record FiniteFamily {A : Set} (P : A -> Set) : Set where
  field
    cardinality : Nat
    enumerate : Fin cardinality -> A
    enumeration-sound :
      (i : Fin cardinality) ->
      P (enumerate i)
    enumeration-complete :
      (x : A) ->
      P x ->
      Exists (Fin cardinality) (\ i -> enumerate i == x)
    enumeration-injective :
      (i j : Fin cardinality) ->
      enumerate i == enumerate j ->
      i == j

open FiniteFamily using (cardinality)

record EulerPartitionResult (n : Nat) : Set where
  field
    distinct-partitions :
      FiniteFamily (IsDistinctPartition n)
    odd-partitions :
      FiniteFamily (IsOddPartition n)
    equal-cardinality :
      cardinality distinct-partitions ==
      cardinality odd-partitions

euler-partition-theorem : Set
euler-partition-theorem =
  (n : Nat) ->
  EulerPartitionResult n
