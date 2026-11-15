-- Statement-only formalization of PutnamBench corpus artifact putnam_2014_b1
-- (putnambench__agda__putnam_2014_b1): positive integers with a unique
-- base-10 over-expansion are exactly those whose ordinary decimal expansion
-- has no zero digit. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_ _<N_
infixr 3 _and_
infix 2 _iff_

data Bottom : Set where

record Top : Set where
  constructor truth

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record _iff_ (A B : Set) : Set where
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record ExistsUnique (A : Set) (P : A -> Set) : Set where
  field
    unique-value    : A
    unique-property : P unique-value
    uniqueness      : (other : A) -> P other -> other == unique-value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

Positive : Nat -> Set
Positive n =
  zero <N n

All : {A : Set} -> (A -> Set) -> List A -> Set
All P [] =
  Top
All P (x ∷ xs) =
  P x and All P xs

LeadingNonzero : List Nat -> Set
LeadingNonzero [] =
  Bottom
LeadingNonzero (digit ∷ []) =
  digit != zero
LeadingNonzero (digit ∷ next ∷ rest) =
  LeadingNonzero (next ∷ rest)

decimalValue : List Nat -> Nat
decimalValue [] =
  zero
decimalValue (digit ∷ rest) =
  digit + 10 * decimalValue rest

OverExpansionDigit : Nat -> Set
OverExpansionDigit digit =
  digit <=N 10

OrdinaryDecimalDigit : Nat -> Set
OrdinaryDecimalDigit digit =
  digit <N 10

NonzeroDigit : Nat -> Set
NonzeroDigit digit =
  digit != zero

OverExpansion : Nat -> List Nat -> Set
OverExpansion N digits =
  decimalValue digits == N
  and
  (LeadingNonzero digits
  and
  All OverExpansionDigit digits)

ZeroFreeOrdinaryExpansion : Nat -> List Nat -> Set
ZeroFreeOrdinaryExpansion N digits =
  decimalValue digits == N
  and
  (LeadingNonzero digits
  and
  (All OrdinaryDecimalDigit digits
  and
  All NonzeroDigit digits))

UniqueOverExpansion : Nat -> Set
UniqueOverExpansion N =
  ExistsUnique (List Nat) (OverExpansion N)

HasZeroFreeOrdinaryExpansion : Nat -> Set
HasZeroFreeOrdinaryExpansion N =
  Exists (List Nat) (ZeroFreeOrdinaryExpansion N)

putnam-2014-b1 : Set
putnam-2014-b1 =
  (N : Nat) ->
  (Positive N and UniqueOverExpansion N)
  iff
  (Positive N and HasZeroFreeOrdinaryExpansion N)
