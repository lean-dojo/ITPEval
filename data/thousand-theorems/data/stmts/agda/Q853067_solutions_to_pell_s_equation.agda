-- Statement-only formalization of thousand-theorems corpus artifact Q853067
-- (thousand-theorems__agda__Q853067), "Solutions to Pell's equation": every
-- natural solution of the Pell equation with parameter a * a - 1 is generated
-- by the recursive Pell sequence. This file contains no proof.

{-# OPTIONS --safe #-}

module Q853067_solutions_to_pell_s_equation where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=_ _<_
infixr 3 _and_

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

record _and_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value : A
    property : P value

one : Nat
one =
  suc zero

natSub : Nat -> Nat -> Nat
natSub n zero =
  n
natSub zero (suc n) =
  zero
natSub (suc m) (suc n) =
  natSub m n

record NatPair : Set where
  constructor pair
  field
    pairX : Nat
    pairY : Nat

open NatPair

d : (a : Nat) -> one < a -> Nat
d a a1 =
  natSub (a * a) one

pell : (a : Nat) -> (a1 : one < a) -> Nat -> NatPair
pell a a1 zero =
  pair one zero
pell a a1 (suc n) with pell a a1 n
... | pair x y =
  pair
    (x * a + d a a1 * y)
    (x + y * a)

xn : (a : Nat) -> one < a -> Nat -> Nat
xn a a1 n =
  pairX (pell a a1 n)

yn : (a : Nat) -> one < a -> Nat -> Nat
yn a a1 n =
  pairY (pell a a1 n)

PellEquation : (a : Nat) -> one < a -> Nat -> Nat -> Set
PellEquation a a1 x y =
  natSub (x * x) (d a a1 * y * y) == one

SolutionsToPellsEquation : Set
SolutionsToPellsEquation =
  (a : Nat) ->
  (a1 : one < a) ->
  (x y : Nat) ->
  PellEquation a a1 x y ->
  Exists Nat
    (λ n ->
      (x == xn a a1 n) and
      (y == yn a a1 n))
