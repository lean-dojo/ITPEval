-- Statement-only formalization of PutnamBench corpus artifact putnam_1974_b6:
-- the subsets of a 1000-element set whose cardinalities are congruent to
-- 0, 1, and 2 modulo 3 have the stated three exact counts.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value : A
    property : P value

record HasExtensionalCardinality
  {A : Set}
  (equivalent : A → A → Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality →
      A

    enumeration-complete :
      (item : A) →
      Exists (Fin cardinality)
        (λ index → equivalent item (enumerate index))

    enumeration-injective :
      (left-index right-index : Fin cardinality) →
      equivalent (enumerate left-index) (enumerate right-index) →
      left-index ≡ right-index

record Subset (n : Nat) : Set where
  constructor subset
  field
    contains : Fin n → Bool

open Subset

countTrue :
  {n : Nat} →
  (Fin n → Bool) →
  Nat
countTrue {zero} membership =
  zero
countTrue {suc n} membership with membership fzero
... | false =
  countTrue (λ index → membership (fsuc index))
... | true =
  suc (countTrue (λ index → membership (fsuc index)))

subsetCardinality :
  {n : Nat} →
  Subset n →
  Nat
subsetCardinality finiteSubset =
  countTrue (contains finiteSubset)

three : Nat
three =
  suc (suc (suc zero))

CongruentModuloThree :
  Nat →
  Nat →
  Set
CongruentModuloThree cardinality residue =
  Exists Nat
    (λ quotient →
      cardinality ≡ three * quotient + residue)

record ResidueSubset (n residue : Nat) : Set where
  constructor residueSubset
  field
    finiteSubset : Subset n
    residue-equation :
      CongruentModuloThree
        (subsetCardinality finiteSubset)
        residue

open ResidueSubset

SameResidueSubset :
  {n residue : Nat} →
  ResidueSubset n residue →
  ResidueSubset n residue →
  Set
SameResidueSubset {n} left right =
  (index : Fin n) →
  contains (finiteSubset left) index ≡
  contains (finiteSubset right) index

ResidueFamily :
  Nat →
  Nat →
  Nat →
  Set
ResidueFamily n residue cardinality =
  HasExtensionalCardinality
    {A = ResidueSubset n residue}
    SameResidueSubset
    cardinality

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

thousand : Nat
thousand =
  1000

power :
  Nat →
  Nat →
  Nat
power base zero =
  one
power base (suc exponent) =
  base * power base exponent

divideByThree : Nat → Nat
divideByThree zero =
  zero
divideByThree (suc zero) =
  zero
divideByThree (suc (suc zero)) =
  zero
divideByThree (suc (suc (suc n))) =
  suc (divideByThree n)

solutionBase : Nat
solutionBase =
  divideByThree (power two thousand - one)

record NatTriple : Set where
  constructor triple
  field
    first second third-component : Nat

putnam-1974-b6-solution : NatTriple
putnam-1974-b6-solution =
  triple
    solutionBase
    solutionBase
    (suc solutionBase)

putnam-1974-b6 : Set
putnam-1974-b6 =
  (count0 count1 count2 : Nat) →
  ResidueFamily thousand zero count0 →
  ResidueFamily thousand one count1 →
  ResidueFamily thousand two count2 →
  triple count0 count1 count2 ≡
  putnam-1974-b6-solution
