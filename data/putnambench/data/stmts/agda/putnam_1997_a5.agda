-- Statement-only formalization of PutnamBench corpus artifact
-- putnambench__agda__putnam_1997_a5: the set of ordered ten-tuples of positive
-- integers whose reciprocals sum to one has odd cardinality. This file contains
-- no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 3 _and_

record _and_ (A B : Set) : Set where
  constructor both
  field
    left-proof  : A
    right-proof : B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

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

data PositiveNat : Set where
  positive : Nat -> PositiveNat

positiveValue : PositiveNat -> Nat
positiveValue (positive predecessor) =
  suc predecessor

record Tuple10 : Set where
  constructor tuple10
  field
    entry1  : PositiveNat
    entry2  : PositiveNat
    entry3  : PositiveNat
    entry4  : PositiveNat
    entry5  : PositiveNat
    entry6  : PositiveNat
    entry7  : PositiveNat
    entry8  : PositiveNat
    entry9  : PositiveNat
    entry10 : PositiveNat

open Tuple10

record FractionExpression : Set where
  constructor fraction
  field
    numerator   : Nat
    denominator : Nat

open FractionExpression

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

oneFraction : FractionExpression
oneFraction =
  fraction oneN oneN

reciprocal : PositiveNat -> FractionExpression
reciprocal denominatorValue =
  fraction oneN (positiveValue denominatorValue)

addFraction :
  FractionExpression ->
  FractionExpression ->
  FractionExpression
addFraction left right =
  fraction
    (numerator left * denominator right
     + numerator right * denominator left)
    (denominator left * denominator right)

EquivalentFraction :
  FractionExpression ->
  FractionExpression ->
  Set
EquivalentFraction left right =
  numerator left * denominator right
  ==
  numerator right * denominator left

reciprocalSum : Tuple10 -> FractionExpression
reciprocalSum tuple =
  addFraction
    (reciprocal (entry1 tuple))
    (addFraction
      (reciprocal (entry2 tuple))
      (addFraction
        (reciprocal (entry3 tuple))
        (addFraction
          (reciprocal (entry4 tuple))
          (addFraction
            (reciprocal (entry5 tuple))
            (addFraction
              (reciprocal (entry6 tuple))
              (addFraction
                (reciprocal (entry7 tuple))
                (addFraction
                  (reciprocal (entry8 tuple))
                  (addFraction
                    (reciprocal (entry9 tuple))
                    (reciprocal (entry10 tuple))))))))))

ReciprocalsSumToOne : Tuple10 -> Set
ReciprocalsSumToOne tuple =
  EquivalentFraction
    (reciprocalSum tuple)
    oneFraction

Odd : Nat -> Set
Odd cardinality =
  Exists Nat
    (\ k -> cardinality == suc (twoN * k))

OddCardinality :
  {A : Set} ->
  (A -> Set) ->
  Set
OddCardinality member =
  Exists Nat
    (\ cardinality ->
      HasCardinality member cardinality
      and
      Odd cardinality)

putnam-1997-a5 : Set
putnam-1997-a5 =
  OddCardinality ReciprocalsSumToOne
