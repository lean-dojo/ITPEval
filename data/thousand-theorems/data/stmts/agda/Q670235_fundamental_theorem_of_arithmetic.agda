-- Statement-only formalization of thousand-theorems corpus artifact
-- thousand-theorems__agda__Q670235, "Fundamental theorem of arithmetic":
-- every prime list whose product is n is a permutation of the canonical list
-- obtained by repeatedly extracting the least divisor. This file contains no proof.

{-# OPTIONS --safe #-}

module Q670235_fundamental_theorem_of_arithmetic where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _*_; div-helper; mod-helper)

infix 4 _<=_ _divides_ _member_
infixr 3 _or_

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

data _or_ (A B : Set) : Set where
  left : A -> A or B
  right : B -> A or B

record _divides_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    division-equation : divisor * quotient == dividend

record Prime (p : Nat) : Set where
  field
    at-least-two : 2 <= p
    only-trivial-divisors :
      (d : Nat) ->
      d divides p ->
      (d == 1) or (d == p)

data List (A : Set) : Set where
  nil : List A
  cons : A -> List A -> List A

data _member_ {A : Set} (x : A) : List A -> Set where
  here : {xs : List A} -> x member (cons x xs)
  there :
    {y : A} ->
    {xs : List A} ->
    x member xs ->
    x member (cons y xs)

product : List Nat -> Nat
product nil =
  1
product (cons p factors) =
  p * product factors

naturalDiv : Nat -> Nat -> Nat
naturalDiv numerator zero =
  zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

natEqual : Nat -> Nat -> Bool
natEqual zero zero =
  true
natEqual zero (suc n) =
  false
natEqual (suc m) zero =
  false
natEqual (suc m) (suc n) =
  natEqual m n

smallestDivisorFrom : Nat -> Nat -> Nat -> Nat
smallestDivisorFrom value candidate zero =
  value
smallestDivisorFrom value candidate (suc fuel)
  with natEqual (naturalMod value candidate) zero
... | true =
  candidate
... | false =
  smallestDivisorFrom value (suc candidate) fuel

smallestDivisor : Nat -> Nat
smallestDivisor value =
  smallestDivisorFrom value 2 value

primeFactorsWithFuel : Nat -> Nat -> List Nat
primeFactorsWithFuel zero value =
  nil
primeFactorsWithFuel (suc fuel) zero =
  nil
primeFactorsWithFuel (suc fuel) (suc zero) =
  nil
primeFactorsWithFuel (suc fuel) value@(suc (suc n)) =
  cons
    (smallestDivisor value)
    (primeFactorsWithFuel fuel
      (naturalDiv value (smallestDivisor value)))

primeFactorsList : Nat -> List Nat
primeFactorsList n =
  primeFactorsWithFuel n n

data Permutation {A : Set} : List A -> List A -> Set where
  empty-permutation :
    Permutation nil nil
  prepend-same :
    {left-list right-list : List A} ->
    (x : A) ->
    Permutation left-list right-list ->
    Permutation (cons x left-list) (cons x right-list)
  swap-adjacent :
    (x y : A) ->
    (rest : List A) ->
    Permutation
      (cons x (cons y rest))
      (cons y (cons x rest))
  transitive-permutation :
    {first second third : List A} ->
    Permutation first second ->
    Permutation second third ->
    Permutation first third

fundamental-theorem-of-arithmetic : Set
fundamental-theorem-of-arithmetic =
  (n : Nat) ->
  (factors : List Nat) ->
  product factors == n ->
  ((p : Nat) -> p member factors -> Prime p) ->
  Permutation factors (primeFactorsList n)
