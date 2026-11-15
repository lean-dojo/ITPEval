-- Statement-only formalization of PutnamBench corpus artifact
-- putnambench__agda__putnam_1991_a6: equality of two counts of positive
-- integer compositions governed by gap and recurrence conditions.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1991A6 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_)

infix 4 _<N_ _<=N_
infixr 3 _and_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

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

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

finToNat :
  {n : Nat} ->
  Fin n ->
  Nat
finToNat fzero =
  zero
finToNat (fsuc index) =
  suc (finToNat index)

sumFin :
  {n : Nat} ->
  (Fin n -> Nat) ->
  Nat
sumFin {zero} terms =
  zero
sumFin {suc n} terms =
  terms fzero + sumFin (\ index -> terms (fsuc index))

record Composition : Set where
  constructor composition
  field
    length : Nat
    terms  : Nat -> Nat

open Composition

record SameComposition
  (left right : Composition) :
  Set where

  field
    same-length :
      length left == length right
    same-terms :
      (index : Nat) ->
      terms left index == terms right index

record HasExtensionalCardinality
  {A : Set}
  (equivalent : A -> A -> Set)
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
        (\ index -> equivalent item (enumerate index))
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      equivalent (enumerate left-index) (enumerate right-index) ->
      left-index == right-index

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

PositiveCompositionOf :
  Nat ->
  Composition ->
  Set
PositiveCompositionOf n parts =
  one <=N length parts
  and
  ((index : Nat) ->
    index <N length parts ->
    zero <N terms parts index)
  and
  ((index : Nat) ->
    length parts <=N index ->
    terms parts index == zero)
  and
  sumFin {n = length parts}
    (\ index ->
      terms parts (finToNat index))
  == n

StrongGap :
  Composition ->
  Set
StrongGap parts =
  ((index : Nat) ->
    index <N (length parts - two) ->
    terms parts (index + one) + terms parts (index + two)
      <N terms parts index)
  and
  (one <N length parts ->
    terms parts (length parts - one)
      <N terms parts (length parts - two))

Nonincreasing :
  Composition ->
  Set
Nonincreasing parts =
  (index : Nat) ->
  index <N (length parts - one) ->
  terms parts (index + one) <=N terms parts index

UsesSequence :
  (Nat -> Nat) ->
  Composition ->
  Set
UsesSequence g parts =
  (index : Nat) ->
  index <N length parts ->
  Exists Nat
    (\ sequence-index ->
      terms parts index == g sequence-index)

CoversInitialSegment :
  (Nat -> Nat) ->
  Composition ->
  Set
CoversInitialSegment g parts =
  Exists Nat
    (\ largest-index ->
      terms parts zero == g largest-index
      and
      ((sequence-index : Nat) ->
        sequence-index <=N largest-index ->
        Exists Nat
          (\ part-index ->
            part-index <N length parts
            and
            terms parts part-index == g sequence-index)))

FirstFamily :
  Nat ->
  Composition ->
  Set
FirstFamily n parts =
  PositiveCompositionOf n parts
  and
  StrongGap parts

SecondFamily :
  (Nat -> Nat) ->
  Nat ->
  Composition ->
  Set
SecondFamily g n parts =
  PositiveCompositionOf n parts
  and
  Nonincreasing parts
  and
  UsesSequence g parts
  and
  CoversInitialSegment g parts

RecurrenceSequence :
  (Nat -> Nat) ->
  Set
RecurrenceSequence g =
  g zero == one
  and
  g one == two
  and
  ((index : Nat) ->
    two <=N index ->
    g index ==
      g (index - one) + g (index - two) + one)

FirstFamilyCount :
  (Nat -> Nat) ->
  Set
FirstFamilyCount A =
  (n : Nat) ->
  one <=N n ->
  HasExtensionalCardinality
    SameComposition
    (FirstFamily n)
    (A n)

SecondFamilyCount :
  (Nat -> Nat) ->
  (Nat -> Nat) ->
  Set
SecondFamilyCount g B =
  (n : Nat) ->
  one <=N n ->
  HasExtensionalCardinality
    SameComposition
    (SecondFamily g n)
    (B n)

putnam-1991-a6 : Set
putnam-1991-a6 =
  (A g B : Nat -> Nat) ->
  FirstFamilyCount A ->
  RecurrenceSequence g ->
  SecondFamilyCount g B ->
  (n : Nat) ->
  one <=N n ->
  A n == B n
