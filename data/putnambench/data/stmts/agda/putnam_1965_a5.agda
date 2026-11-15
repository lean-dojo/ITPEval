-- Statement-only formalization of PutnamBench corpus artifact putnam_1965_a5:
-- the number of orderings of 1 through n in which every entry after the first
-- differs by one from an earlier entry is 2^(n-1). This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1965A5 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _<N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

NotEqual : {A : Set} -> A -> A -> Set
NotEqual x y =
  x == y -> Bottom

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

data _<N_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero <N suc n
  suc<suc  : {m n : Nat} -> m <N n -> suc m <N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

toNat : {n : Nat} -> Fin n -> Nat
toNat fzero =
  zero
toNat (fsuc index) =
  suc (toNat index)

record Bijection (A B : Set) : Set where
  field
    to      : A -> B
    from    : B -> A
    from-to : (x : A) -> from (to x) == x
    to-from : (y : B) -> to (from y) == y

Adjacent : Nat -> Nat -> Set
Adjacent x y =
  x == suc y or y == suc x

record AdmissiblePermutation (n : Nat) : Set where
  field
    permutation : Bijection (Fin n) (Fin n)
    earlier-adjacent :
      (index : Fin n) ->
      zero <N toNat index ->
      Exists (Fin n)
        (\ earlier ->
          toNat earlier <N toNat index
          and
          Adjacent
            (toNat (Bijection.to permutation index))
            (toNat (Bijection.to permutation earlier)))

SameAdmissiblePermutation :
  {n : Nat} ->
  AdmissiblePermutation n ->
  AdmissiblePermutation n ->
  Set
SameAdmissiblePermutation {n} left-permutation right-permutation =
  (index : Fin n) ->
  Bijection.to
    (AdmissiblePermutation.permutation left-permutation)
    index
  ==
  Bijection.to
    (AdmissiblePermutation.permutation right-permutation)
    index

record HasExtensionalCardinality
  {A : Set}
  (equivalent : A -> A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A
    enumeration-complete :
      (item : A) ->
      Exists (Fin cardinality)
        (\ index -> equivalent item (enumerate index))
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      equivalent (enumerate left-index) (enumerate right-index) ->
      left-index == right-index

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

predecessor : Nat -> Nat
predecessor zero =
  zero
predecessor (suc n) =
  n

power : Nat -> Nat -> Nat
power base zero =
  one
power base (suc exponent) =
  base * power base exponent

putnam-1965-a5 : Set
putnam-1965-a5 =
  (n : Nat) ->
  NotEqual n zero ->
  HasExtensionalCardinality
    {A = AdmissiblePermutation n}
    SameAdmissiblePermutation
    (power two (predecessor n))
