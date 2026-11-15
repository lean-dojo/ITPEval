-- Statement-only formalization of PutnamBench corpus artifact putnam_1980_a2:
-- the number of ordered quadruples of positive natural numbers for which every
-- triple has least common multiple 3^r * 7^s. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=N_ _<N_ _divides_
infixr 8 _^_

data _<=N_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n = suc m <=N n

_^_ : Nat -> Nat -> Nat
base ^ zero = 1
base ^ suc exponent = base * (base ^ exponent)

record _divides_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient == dividend

record IsTripleLCM (a b c l : Nat) : Set where
  field
    first-divides : a divides l
    second-divides : b divides l
    third-divides : c divides l
    least :
      (common : Nat) ->
      a divides common ->
      b divides common ->
      c divides common ->
      l divides common

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc : {n : Nat} -> Fin n -> Fin (suc n)

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value : A
    property : P value

record HasCardinality
  {A : Set}
  (P : A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      P (enumerate index)
    enumeration-complete :
      (item : A) ->
      P item ->
      Exists (Fin cardinality)
        (\ index -> item == enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

record Quadruple : Set where
  constructor quadruple
  field
    first : Nat
    second : Nat
    third : Nat
    fourth : Nat

open Quadruple

target : Nat -> Nat -> Nat
target r s =
  (3 ^ r) * (7 ^ s)

record QualifyingQuadruple (r s : Nat) (q : Quadruple) : Set where
  field
    first-positive : zero <N first q
    second-positive : zero <N second q
    third-positive : zero <N third q
    fourth-positive : zero <N fourth q
    first-second-third-lcm :
      IsTripleLCM (first q) (second q) (third q) (target r s)
    first-second-fourth-lcm :
      IsTripleLCM (first q) (second q) (fourth q) (target r s)
    first-third-fourth-lcm :
      IsTripleLCM (first q) (third q) (fourth q) (target r s)
    second-third-fourth-lcm :
      IsTripleLCM (second q) (third q) (fourth q) (target r s)

putnam-1980-a2-solution : Nat -> Nat -> Nat
putnam-1980-a2-solution r s =
  (1 + 4 * r + 6 * (r ^ 2)) *
  (1 + 4 * s + 6 * (s ^ 2))

putnam-1980-a2 : Set
putnam-1980-a2 =
  (r s : Nat) ->
  zero <N r ->
  zero <N s ->
  HasCardinality
    (QualifyingQuadruple r s)
    (putnam-1980-a2-solution r s)
