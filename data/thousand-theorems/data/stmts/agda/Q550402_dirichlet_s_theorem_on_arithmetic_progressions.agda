-- Statement-only formalization of thousand-theorems corpus artifact
-- thousand-theorems__agda__Q550402, "Dirichlet's theorem on arithmetic progressions":
-- for a nonzero modulus and a unit residue class, infinitely many natural primes lie in
-- that residue class. This file contains no proof.

{-# OPTIONS --safe #-}

module Q550402_dirichlet_s_theorem_on_arithmetic_progressions where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _*_; mod-helper)

infix 4 _<=_ _<_ _divides_
infixr 5 _and_
infixr 3 _or_

data Bottom : Set where

Not : Set -> Set
Not proposition =
  proposition -> Bottom

record Exists (A : Set) (property : A -> Set) : Set where
  constructor witness
  field
    value : A
    satisfies : property value

record _and_ (A B : Set) : Set where
  constructor pair
  field
    left : A
    right : B

data _or_ (A B : Set) : Set where
  left : A -> A or B
  right : B -> A or B

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

record _divides_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    division-equation : divisor * quotient == dividend

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

record Prime (p : Nat) : Set where
  field
    at-least-two : two <= p
    only-trivial-divisors :
      (d : Nat) ->
      d divides p ->
      (d == one) or (d == p)

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

ModEq : Nat -> Nat -> Nat -> Set
ModEq modulus lhs rhs =
  naturalMod lhs modulus == naturalMod rhs modulus

record NeZero (q : Nat) : Set where
  field
    nonzero : Not (q == zero)

record ZMod (q : Nat) : Set where
  constructor residue
  field
    representative : Nat
    reduced : representative < q

open ZMod

record IsUnit {q : Nat} (a : ZMod q) : Set where
  field
    inverse : ZMod q
    inverse-equation :
      ModEq q
        (representative a * representative inverse)
        one

Infinite : (Nat -> Set) -> Set
Infinite member =
  (bound : Nat) ->
  Exists Nat
    (\ n ->
      member n and (bound < n))

primeInResidueClass :
  (q : Nat) ->
  ZMod q ->
  Nat ->
  Set
primeInResidueClass q a p =
  Prime p and ModEq q p (representative a)

dirichlet-s-theorem-on-arithmetic-progressions : Set
dirichlet-s-theorem-on-arithmetic-progressions =
  (q : Nat) ->
  NeZero q ->
  (a : ZMod q) ->
  IsUnit a ->
  Infinite (primeInResidueClass q a)
