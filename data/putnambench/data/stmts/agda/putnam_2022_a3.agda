-- Statement-only formalization of PutnamBench corpus artifact putnam_2022_a3:
-- for every prime p greater than 5, the number of nonzero residue sequences
-- satisfying a_n * a_(n+2) = 1 + a_(n+1) modulo p is 0 or 2 modulo 5.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2022A3 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infix 4 _<=N_ _<N_ _divides_
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

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

record _divides_ (divisor dividend : Nat) : Set where
  constructor divides-with
  field
    quotient : Nat
    equation : divisor * quotient == dividend

record Prime (p : Nat) : Set where
  field
    at-least-two :
      suc (suc zero) <=N p

    only-trivial-divisors :
      (d : Nat) ->
      d divides p ->
      d == suc zero or d == p

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

five : Nat
five =
  suc (suc (suc (suc (suc zero))))

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

ModEq : Nat -> Nat -> Nat -> Set
ModEq modulus left-value right-value =
  naturalMod left-value modulus ==
  naturalMod right-value modulus

Sequence : Set
Sequence =
  Nat -> Nat

PointwiseEqual : Sequence -> Sequence -> Set
PointwiseEqual left-sequence right-sequence =
  (n : Nat) ->
  left-sequence n == right-sequence n

ValidSequence : Nat -> Sequence -> Set
ValidSequence p a =
  (n : Nat) ->
  (one <=N a n)
  and
  (a n <N p)
  and
  ModEq
    p
    (a n * a (n + two))
    (one + a (n + one))

record HasValidSequenceCardinality
  (p cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      Sequence

    enumerated-valid :
      (index : Fin cardinality) ->
      ValidSequence p (enumerate index)

    enumeration-complete :
      (a : Sequence) ->
      ValidSequence p a ->
      Exists
        (Fin cardinality)
        (\ index ->
          PointwiseEqual a (enumerate index))

    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      PointwiseEqual
        (enumerate left-index)
        (enumerate right-index) ->
      left-index == right-index

putnam-2022-a3 : Set
putnam-2022-a3 =
  (p f : Nat) ->
  (Prime p and five <N p) ->
  HasValidSequenceCardinality p f ->
  (ModEq five f zero or ModEq five f two)
