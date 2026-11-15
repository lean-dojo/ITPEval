-- Statement-only formalization of thousand-theorems corpus artifact Q1933521
-- (thousand-theorems__agda__Q1933521), "Kleene's recursion theorem": every
-- binary partial-recursive function of a program code and a natural number
-- has a code whose evaluation equals the function applied to that code.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q1933521_kleene_s_recursion_theorem where

open import Agda.Primitive using (lzero; lsuc)
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _<_)

infix 4 _iff_
infix 4 _equivalent_

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

-- The square pairing used by the source Nat.Partrec development.
pairNat : Nat -> Nat -> Nat
pairNat left right with left < right
... | true =
  right * right + left
... | false =
  left * left + left + right

-- Codes for the partial-recursive schemes used by the source development.
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
firstFunction equivalent secondFunction =
  (input output : Nat) ->
  (firstFunction input output) iff (secondFunction input output)

-- Binary partial recursiveness uses the source code encoding and the same
-- universal evaluator.
Partrec2 : (Code -> PartialFunction) -> Set
Partrec2 function =
  Exists Code
    (\ program ->
      (code : Code) ->
      (input output : Nat) ->
      (Evaluates
        program
        (pairNat (encodeCode code) input)
        output)
      iff
      (function code input output))

KleeneSecondRecursionTheorem : Set (lsuc lzero)
KleeneSecondRecursionTheorem =
  (function : Code -> PartialFunction) ->
  Partrec2 function ->
  Exists Code
    (\ code ->
      (evaluate code) equivalent (function code))
