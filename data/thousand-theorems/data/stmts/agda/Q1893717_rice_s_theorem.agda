-- Statement-only formalization of thousand-theorems corpus artifact Q1893717
-- (thousand-theorems__agda__Q1893717), "Rice's theorem": every computably
-- decidable extensional property of partial-recursive natural-number functions
-- that holds for one such function holds for all of them. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1893717_rice_s_theorem where

open import Agda.Primitive using (lzero; lsuc)
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _<_)

infix 4 _iff_
infix 4 _equivalent_

data Bottom : Set where

record _iff_ (A B : Set) : Set where
  constructor equivalence
  field
    forward : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value : A
    property : P value

data Decision (A : Set) : Set where
  yes : A -> Decision A
  no : (A -> Bottom) -> Decision A

-- The square pairing used by the source Nat.Partrec development.
pairNat : Nat -> Nat -> Nat
pairNat left right with left < right
... | true =
  right * right + left
... | false =
  left * left + left + right

-- Codes for a universal system of partial-recursive natural-number functions.
data Code : Set where
  zeroCode : Code
  successorCode : Code
  leftCode : Code
  rightCode : Code
  pairCode : Code -> Code -> Code
  composeCode : Code -> Code -> Code
  primitiveRecursionCode : Code -> Code -> Code
  minimizationCode : Code -> Code

-- A computable numerical encoding of program codes.
encodeCode : Code -> Nat
encodeCode zeroCode =
  0
encodeCode successorCode =
  1
encodeCode leftCode =
  2
encodeCode rightCode =
  3
encodeCode (pairCode firstCode secondCode) =
  2 * (2 * pairNat (encodeCode firstCode) (encodeCode secondCode)) + 4
encodeCode (composeCode firstCode secondCode) =
  2 * (2 * pairNat (encodeCode firstCode) (encodeCode secondCode) + 1) + 4
encodeCode (primitiveRecursionCode firstCode secondCode) =
  (2 * (2 * pairNat (encodeCode firstCode) (encodeCode secondCode)) + 1) + 4
encodeCode (minimizationCode code) =
  (2 * (2 * encodeCode code + 1) + 1) + 4

-- Relational evaluation represents termination with the displayed result.
data Evaluates : Code -> Nat -> Nat -> Set where
  evaluates-zero :
    {input : Nat} ->
    Evaluates zeroCode input zero

  evaluates-successor :
    {input : Nat} ->
    Evaluates successorCode input (suc input)

  evaluates-left :
    {left right : Nat} ->
    Evaluates leftCode (pairNat left right) left

  evaluates-right :
    {left right : Nat} ->
    Evaluates rightCode (pairNat left right) right

  evaluates-pair :
    {firstCode secondCode : Code} ->
    {input firstValue secondValue : Nat} ->
    Evaluates firstCode input firstValue ->
    Evaluates secondCode input secondValue ->
    Evaluates
      (pairCode firstCode secondCode)
      input
      (pairNat firstValue secondValue)

  evaluates-composition :
    {firstCode secondCode : Code} ->
    {input intermediate output : Nat} ->
    Evaluates secondCode input intermediate ->
    Evaluates firstCode intermediate output ->
    Evaluates (composeCode firstCode secondCode) input output

  evaluates-primitive-zero :
    {baseCode stepCode : Code} ->
    {parameter output : Nat} ->
    Evaluates baseCode parameter output ->
    Evaluates
      (primitiveRecursionCode baseCode stepCode)
      (pairNat parameter zero)
      output

  evaluates-primitive-successor :
    {baseCode stepCode : Code} ->
    {parameter index previous output : Nat} ->
    Evaluates
      (primitiveRecursionCode baseCode stepCode)
      (pairNat parameter index)
      previous ->
    Evaluates
      stepCode
      (pairNat parameter (pairNat index previous))
      output ->
    Evaluates
      (primitiveRecursionCode baseCode stepCode)
      (pairNat parameter (suc index))
      output

  evaluates-minimization-zero :
    {code : Code} ->
    {parameter start : Nat} ->
    Evaluates code (pairNat parameter start) zero ->
    Evaluates
      (minimizationCode code)
      (pairNat parameter start)
      start

  evaluates-minimization-successor :
    {code : Code} ->
    {parameter start nonzeroValue output : Nat} ->
    Evaluates code (pairNat parameter start) (suc nonzeroValue) ->
    Evaluates
      (minimizationCode code)
      (pairNat parameter (suc start))
      output ->
    Evaluates
      (minimizationCode code)
      (pairNat parameter start)
      output

PartialFunction : Set (lsuc lzero)
PartialFunction =
  Nat -> Nat -> Set

evaluate : Code -> PartialFunction
evaluate code input output =
  Evaluates code input output

_equivalent_ : PartialFunction -> PartialFunction -> Set
f equivalent g =
  (input output : Nat) ->
  (f input output) iff (g input output)

-- This record represents a subset of extensional partial functions rather
-- than a predicate that can distinguish different graph presentations.
record PartialFunctionProperty : Set (lsuc lzero) where
  constructor function-property
  field
    holds : PartialFunction -> Set
    respects-equivalence :
      {f g : PartialFunction} ->
      f equivalent g ->
      (holds f) iff (holds g)

open PartialFunctionProperty using (holds)

Partrec : PartialFunction -> Set
Partrec function =
  Exists Code
    (\ code -> function equivalent evaluate code)

decisionBit : {A : Set} -> Decision A -> Nat
decisionBit (yes proof) =
  suc zero
decisionBit (no refutation) =
  zero

-- A predicate is computable when it has a decision procedure whose Boolean
-- characteristic function is computed by a partial-recursive program.
record ComputablePredicate (predicate : Code -> Set) : Set where
  constructor computable-predicate
  field
    decide : (code : Code) -> Decision (predicate code)
    characteristicProgram : Code
    computesCharacteristic :
      (code : Code) ->
      (output : Nat) ->
      (Evaluates
        characteristicProgram
        (encodeCode code)
        output)
      iff
      (output == decisionBit (decide code))

RiceTheorem : Set (lsuc lzero)
RiceTheorem =
  (C : PartialFunctionProperty) ->
  ComputablePredicate (\ code -> holds C (evaluate code)) ->
  (f g : PartialFunction) ->
  Partrec f ->
  Partrec g ->
  holds C f ->
  holds C g
