-- Statement-only formalization of thousand-theorems corpus artifact Q3007384
-- (thousand-theorems__agda__Q3007384), "Post's theorem": on every primcodable
-- domain, a decidable predicate is computable exactly when it and its
-- complement are recursively enumerable. This file contains no proof.

{-# OPTIONS --safe #-}

module Q3007384_post_s_theorem where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _<_)

infixr 3 _and_
infix 4 _iff_

data Bottom {p : Level} : Set p where

Not :
  {p : Level} ->
  Set p ->
  Set p
Not {p} proposition =
  proposition -> Bottom {p}

record _and_
  {p q : Level}
  (left-proposition : Set p)
  (right-proposition : Set q) :
  Set (p ⊔ q) where

  constructor both
  field
    first  : left-proposition
    second : right-proposition

record _iff_
  {p q : Level}
  (left-proposition : Set p)
  (right-proposition : Set q) :
  Set (p ⊔ q) where

  constructor equivalence
  field
    forward  : left-proposition -> right-proposition
    backward : right-proposition -> left-proposition

record Exists
  {a p : Level}
  (A : Set a)
  (property : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value     : A
    satisfies : property value

data Maybe {a : Level} (A : Set a) : Set a where
  none : Maybe A
  some : A -> Maybe A

data Decision {p : Level} (proposition : Set p) : Set p where
  yes : proposition -> Decision proposition
  no  : Not proposition -> Decision proposition

-- The square pairing used by Mathlib's natural-number computability model.
pairNat : Nat -> Nat -> Nat
pairNat left right with left < right
... | true =
  right * right + left
... | false =
  left * left + left + right

-- Codes for the zero, successor, projections, pairing, composition,
-- primitive-recursion, and minimization schemes of partial recursion.
data Code : Set where
  zeroCode               : Code
  successorCode          : Code
  leftCode               : Code
  rightCode              : Code
  pairCode               : Code -> Code -> Code
  composeCode            : Code -> Code -> Code
  primitiveRecursionCode : Code -> Code -> Code
  minimizationCode       : Code -> Code

-- The codes not using minimization are exactly the primitive-recursive
-- fragment needed by Mathlib's Primcodable structure.
data PrimitiveCode : Code -> Set where
  primrec-zero :
    PrimitiveCode zeroCode
  primrec-successor :
    PrimitiveCode successorCode
  primrec-left :
    PrimitiveCode leftCode
  primrec-right :
    PrimitiveCode rightCode
  primrec-pair :
    {firstCode secondCode : Code} ->
    PrimitiveCode firstCode ->
    PrimitiveCode secondCode ->
    PrimitiveCode (pairCode firstCode secondCode)
  primrec-composition :
    {firstCode secondCode : Code} ->
    PrimitiveCode firstCode ->
    PrimitiveCode secondCode ->
    PrimitiveCode (composeCode firstCode secondCode)
  primrec-recursion :
    {baseCode stepCode : Code} ->
    PrimitiveCode baseCode ->
    PrimitiveCode stepCode ->
    PrimitiveCode (primitiveRecursionCode baseCode stepCode)

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

encodeMaybe :
  {a : Level} ->
  {A : Set a} ->
  (A -> Nat) ->
  Maybe A ->
  Nat
encodeMaybe encode none =
  zero
encodeMaybe encode (some value) =
  suc (encode value)

-- This is the target-native presentation of Mathlib's Primcodable structure:
-- an Encodable retraction for which encoding after optional decoding is a
-- primitive-recursive natural-number function.
record Primcodable
  {a : Level}
  (A : Set a) :
  Set a where

  field
    encode :
      A -> Nat
    decode :
      Nat -> Maybe A
    decode-encode :
      (value : A) ->
      decode (encode value) == some value
    prim-program :
      Code
    program-is-primrec :
      PrimitiveCode prim-program
    computes-encoded-decode :
      (input output : Nat) ->
      (Evaluates prim-program input output) iff
      (output == encodeMaybe encode (decode input))

open Primcodable using (encode)

decisionBit :
  {p : Level} ->
  {proposition : Set p} ->
  Decision proposition ->
  Nat
decisionBit (yes proof) =
  suc zero
decisionBit (no refutation) =
  zero

-- This reproduces ComputablePred: some decision procedure has a total
-- partial-recursive Boolean characteristic function.
record ComputablePredicate
  {a : Level}
  {A : Set a}
  (coding : Primcodable A)
  (predicate : A -> Set) :
  Set a where

  constructor computable-predicate
  field
    decide :
      (value : A) ->
      Decision (predicate value)
    characteristic-program :
      Code
    computes-characteristic :
      (value : A) ->
      (output : Nat) ->
      (Evaluates
        characteristic-program
        (encode coding value)
        output) iff
      (output == decisionBit (decide value))

-- This is REPred in domain form: the predicate holds exactly when a
-- partial-recursive program terminates on the encoded input.
RecursivelyEnumerable :
  {a : Level} ->
  {A : Set a} ->
  Primcodable A ->
  (A -> Set) ->
  Set a
RecursivelyEnumerable {A = A} coding predicate =
  Exists Code
    (\ program ->
      (value : A) ->
      (predicate value) iff
      Exists Nat
        (\ output ->
          Evaluates program (encode coding value) output))

PostTheorem :
  {a : Level} ->
  Set (lsuc a)
PostTheorem {a} =
  (A : Set a) ->
  (coding : Primcodable A) ->
  (predicate : A -> Set) ->
  ((value : A) -> Decision (predicate value)) ->
  (ComputablePredicate coding predicate) iff
  ((RecursivelyEnumerable coding predicate) and
   (RecursivelyEnumerable coding (\ value -> Not (predicate value))))
