-- Statement-only formalization of PutnamBench corpus artifact putnam_1991_b5:
-- for every odd prime p, the residue classes modulo p that are both a square
-- and one more than a square have cardinality p / 4 + 1. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; div-helper; mod-helper)

infix 4 _<=_ _<_ _divides_
infixr 3 _and_
infixr 2 _or_

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

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

record _divides_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    division-equation : dividend == divisor * quotient

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

three : Nat
three =
  suc two

four : Nat
four =
  suc three

record Odd (n : Nat) : Set where
  field
    half : Nat
    odd-equation : n == two * half + one

record Prime (p : Nat) : Set where
  field
    at-least-two : two <= p
    only-trivial-divisors :
      (d : Nat) ->
      d divides p ->
      (d == one) or (d == p)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

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

ModEq : Nat -> Nat -> Nat -> Set
ModEq modulus lhs rhs =
  naturalMod lhs modulus == naturalMod rhs modulus

IsSquareResidue : Nat -> Nat -> Set
IsSquareResidue p z =
  Exists Nat
    (\ x ->
      x < p
      and
      ModEq p z (x * x))

IsOneMoreThanSquareResidue : Nat -> Nat -> Set
IsOneMoreThanSquareResidue p z =
  Exists Nat
    (\ y ->
      y < p
      and
      ModEq p z (y * y + one))

QuadraticIntersection : Nat -> Nat -> Set
QuadraticIntersection p z =
  z < p
  and
  IsSquareResidue p z
  and
  IsOneMoreThanSquareResidue p z

putnam-1991-b5-solution : Nat -> Nat
putnam-1991-b5-solution p =
  naturalDiv p four + one

putnam-1991-b5 : Set
putnam-1991-b5 =
  (p : Nat) ->
  Odd p ->
  Prime p ->
  HasCardinality
    (QuadraticIntersection p)
    (putnam-1991-b5-solution p)
