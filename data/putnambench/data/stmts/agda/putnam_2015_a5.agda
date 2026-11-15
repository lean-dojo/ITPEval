-- Statement-only formalization of PutnamBench corpus artifact putnam_2015_a5
-- (putnambench__agda__putnam_2015_a5): parity of the number of positive
-- integers below q/4 and coprime to odd q, characterized by prime powers
-- whose prime is 5 or 7 modulo 8. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2015A5 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infix 4 _<=_ _<_ _divides_
infixr 8 _pow_
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

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

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

Positive : Nat -> Set
Positive n =
  zero < n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record HasCardinality
  (member : Nat -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      Nat
    enumerated-member :
      (index : Fin cardinality) ->
      member (enumerate index)
    enumeration-complete :
      (item : Nat) ->
      member item ->
      Exists (Fin cardinality)
        (\ index -> item == enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

_divides_ : Nat -> Nat -> Set
divisor divides dividend =
  Exists Nat
    (\ quotient -> dividend == divisor * quotient)

data Prime (n : Nat) : Set where
  prime :
    2 <= n ->
    ((d : Nat) ->
      d divides n ->
      (d == 1) or (d == n)) ->
    Prime n

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

gcdWithFuel : Nat -> Nat -> Nat -> Nat
gcdWithFuel zero a b =
  a
gcdWithFuel (suc fuel) a zero =
  a
gcdWithFuel (suc fuel) a (suc b) =
  gcdWithFuel fuel (suc b) (naturalMod a (suc b))

naturalGCD : Nat -> Nat -> Nat
naturalGCD a b =
  gcdWithFuel (suc (a + b)) a b

_pow_ : Nat -> Nat -> Nat
base pow zero =
  1
base pow (suc exponent) =
  base * (base pow exponent)

Odd : Nat -> Set
Odd n =
  Exists Nat
    (\ half -> n == 2 * half + 1)

Eligible : Nat -> Nat -> Set
Eligible q a =
  Positive a
  and
  ((4 * a < q)
  and
  (naturalGCD a q == 1))

PrimePowerResidue : Nat -> Set
PrimePowerResidue q =
  Exists Nat
    (\ p ->
      Exists Nat
        (\ k ->
          (q == p pow k)
          and
          (Positive k
          and
          (Prime p
          and
          ((naturalMod p 8 == 5)
          or
          (naturalMod p 8 == 7))))))

putnam-2015-a5 : Set
putnam-2015-a5 =
  (q Nq : Nat) ->
  Odd q ->
  Positive q ->
  HasCardinality (Eligible q) Nq ->
  Iff (Odd Nq) (PrimePowerResidue q)
