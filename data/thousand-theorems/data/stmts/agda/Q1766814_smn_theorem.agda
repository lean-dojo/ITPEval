-- Statement-only formalization of thousand-theorems corpus artifact Q1766814
-- (thousand-theorems__agda__Q1766814), "Smn theorem": there exists a computable
-- program-specialization function whose evaluation fixes the first input of
-- every partial-recursive program. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1766814_smn_theorem where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _<_)

infixr 3 _and_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value : A
    property : P value

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward : A -> B
    backward : B -> A

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

-- Relational evaluation represents termination of a partial computation.
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

-- Binary computability uses the same code interpretation and code encoding.
record Computable2 (function : Code -> Nat -> Code) : Set where
  constructor computed-by
  field
    program : Code
    computes :
      (code : Code) ->
      (argument : Nat) ->
      Evaluates
        program
        (pairNat (encodeCode code) argument)
        (encodeCode (function code argument))

SmnTheorem : Set
SmnTheorem =
  Exists
    (Code -> Nat -> Code)
    (\ specialize ->
      Computable2 specialize and
      ((code : Code) ->
       (fixed argument output : Nat) ->
       Iff
         (Evaluates (specialize code fixed) argument output)
         (Evaluates code (pairNat fixed argument) output)))
