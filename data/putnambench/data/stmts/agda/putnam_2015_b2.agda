-- Statement-only formalization of PutnamBench corpus artifact putnam_2015_b2
-- (putnambench__agda__putnam_2015_b2): repeatedly remove the three least
-- positive integers still present and their sum; some resulting sum is
-- congruent to 2015 modulo 10000. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2015B2 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; mod-helper)

infix 4 _!=_ _<=N_
infixr 3 _and_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record _and_ (A B : Set) : Set where
  constructor both
  field
    left-conjunct  : A
    right-conjunct : B

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

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

SetOfNaturals : Set1
SetOfNaturals =
  Nat -> Set

SameSet : SetOfNaturals -> SetOfNaturals -> Set
SameSet left right =
  (x : Nat) -> Iff (left x) (right x)

PositiveNaturals : SetOfNaturals
PositiveNaturals x =
  suc zero <=N x

DeleteOne : SetOfNaturals -> Nat -> SetOfNaturals
DeleteOne S removed x =
  S x and x != removed

DeleteFour :
  SetOfNaturals ->
  Nat ->
  Nat ->
  Nat ->
  Nat ->
  SetOfNaturals
DeleteFour S a b c d x =
  S x
  and
  (x != a
  and
  (x != b
  and
  (x != c
  and
  x != d)))

record HasAtLeastThree (S : SetOfNaturals) : Set where
  field
    first-member  : Nat
    second-member : Nat
    third-member  : Nat
    first-present  : S first-member
    second-present : S second-member
    third-present  : S third-member
    first-second-distinct : first-member != second-member
    first-third-distinct  : first-member != third-member
    second-third-distinct : second-member != third-member

Least : SetOfNaturals -> Nat -> Set
Least S candidate =
  S candidate
  and
  ((x : Nat) -> S x -> candidate <=N x)

record Triple : Set where
  constructor triple
  field
    first-value  : Nat
    second-value : Nat
    third-value  : Nat

open Triple

record ThreeSmallest
  (S : SetOfNaturals)
  (values : Triple) :
  Set where

  field
    first-is-least :
      Least S (first-value values)
    second-is-least :
      Least
        (DeleteOne S (first-value values))
        (second-value values)
    third-is-least :
      Least
        (DeleteOne
          (DeleteOne S (first-value values))
          (second-value values))
        (third-value values)

tripleSum : Triple -> Nat
tripleSum values =
  first-value values + second-value values + third-value values

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

putnam-2015-b2 : Set1
putnam-2015-b2 =
  (sets : Nat -> SetOfNaturals) ->
  (smallestThree : SetOfNaturals -> Triple) ->
  (sums : Nat -> Nat) ->
  SameSet (sets zero) PositiveNaturals ->
  ((S : SetOfNaturals) ->
    HasAtLeastThree S ->
    ThreeSmallest S (smallestThree S)) ->
  ((n : Nat) ->
    sums n == tripleSum (smallestThree (sets n))) ->
  ((n : Nat) ->
    SameSet
      (sets (suc n))
      (DeleteFour
        (sets n)
        (first-value (smallestThree (sets n)))
        (second-value (smallestThree (sets n)))
        (third-value (smallestThree (sets n)))
        (sums n))) ->
  Exists Nat
    (\ n -> naturalMod (sums n) 10000 == 2015)
