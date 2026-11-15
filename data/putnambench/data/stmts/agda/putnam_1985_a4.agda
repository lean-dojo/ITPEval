-- Statement-only formalization of PutnamBench corpus artifact putnam_1985_a4:
-- for the sequence beginning at 3 and iterating exponentiation by 3, the
-- unique last-two-digit residue occurring infinitely often is 87. This file
-- contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infix 4 _<=N_ _<N_
infixr 3 _and_
infix 1 _iff_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record _iff_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

one three eightySeven hundred : Nat
one =
  suc zero
three =
  suc (suc one)
eightySeven =
  87
hundred =
  100

naturalPower : Nat -> Nat -> Nat
naturalPower base zero =
  one
naturalPower base (suc exponent) =
  base * naturalPower base exponent

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

RecurringResidue : (Nat -> Nat) -> Nat -> Set
RecurringResidue a k =
  k <N hundred
  and
  ((N : Nat) ->
    Exists Nat
      (\ i ->
        N <=N i
        and
        naturalMod (a i) hundred == k))

putnam-1985-a4 : Set
putnam-1985-a4 =
  (a : Nat -> Nat) ->
  a one == three ->
  ((i : Nat) ->
    one <=N i ->
    a (i + one) == naturalPower three (a i)) ->
  (k : Nat) ->
  _iff_ (RecurringResidue a k) (k == eightySeven)
