-- Statement-only formalization of thousand-theorems corpus artifact Q16251580
-- (thousand-theorems__agda__Q16251580), "Matiyasevich's theorem": Davis's
-- Pell-sequence characterization of a system of natural-number Diophantine
-- equations and congruences. This file contains no proof.

{-# OPTIONS --safe #-}

module Q16251580_matiyasevich_s_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infix 4 _<=_ _<_ _divides_
infixr 3 _and_
infixr 2 _or_

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

data _or_ (A B : Set) : Set where
  left : A -> A or B
  right : B -> A or B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value : A
    property : P value

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward : A -> B
    backward : B -> A

one : Nat
one =
  suc zero

four : Nat
four =
  suc (suc (suc one))

natSub : Nat -> Nat -> Nat
natSub n zero =
  n
natSub zero (suc n) =
  zero
natSub (suc m) (suc n) =
  natSub m n

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

ModEq : Nat -> Nat -> Nat -> Set
ModEq modulus lhs rhs =
  naturalMod lhs modulus == naturalMod rhs modulus

_divides_ : Nat -> Nat -> Set
divisor divides dividend =
  Exists Nat (λ quotient -> dividend == divisor * quotient)

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

PellMembership : Nat -> Nat -> Nat -> Nat -> Set
PellMembership a k x y =
  Exists (one < a)
    (λ a1 -> (xn a a1 k == x) and (yn a a1 k == y))

PellEquation : Nat -> Nat -> Nat -> Set
PellEquation parameter x y =
  natSub
    (x * x)
    (natSub (parameter * parameter) one * y * y)
  == one

DiophantineSystem : Nat -> Nat -> Nat -> Nat -> Set
DiophantineSystem a k x y =
  Exists Nat (λ u ->
  Exists Nat (λ v ->
  Exists Nat (λ s ->
  Exists Nat (λ t ->
  Exists Nat (λ b ->
    PellEquation a x y
    and PellEquation a u v
    and PellEquation b s t
    and one < b
    and ModEq (four * y) b one
    and ModEq u b a
    and zero < v
    and (y * y) divides v
    and ModEq u s x
    and ModEq (four * y) t k)))))

MatiyasevichTheorem : Set
MatiyasevichTheorem =
  (a k x y : Nat) ->
  Iff
    (PellMembership a k x y)
    (one < a
      and k <= y
      and ((x == one and y == zero)
        or DiophantineSystem a k x y))
