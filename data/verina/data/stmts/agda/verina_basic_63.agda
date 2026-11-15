-- Statement-only formalization of VERINA corpus artifact verina_basic_63,
-- catalog title "has_close_elements": a deterministic scan of finite
-- IEEE-754 floating-point values detects whether an earlier/later pair has
-- absolute difference below a nonnegative threshold and is connected to its
-- pairwise separation correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic63 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Float using
  ( Float
  ; primFloatEquality
  ; primFloatIsInfinite
  ; primFloatIsNaN
  ; primFloatLess
  ; primFloatMinus
  ; primNatToFloat
  )
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (zero)

infix 2 _↔_
infixr 3 _∧_
infixr 5 _++_

record Top : Set where
  constructor top

data Empty : Set where

Not : Set → Set
Not A = A → Empty

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

record _↔_ (A B : Set) : Set where
  constructor equivalence
  field
    forward : A → B
    backward : B → A

data IsTrue : Bool → Set where
  true-witness : IsTrue true

IsFalse : Bool → Set
IsFalse condition = Not (IsTrue condition)

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

boolOr : Bool → Bool → Bool
boolOr true right = true
boolOr false right = right

floatLessOrEqual : Float → Float → Bool
floatLessOrEqual x y =
  boolOr
    (primFloatLess x y)
    (primFloatEquality x y)

FloatLessOrEqual : Float → Float → Set
FloatLessOrEqual x y =
  IsTrue (floatLessOrEqual x y)

FloatGreaterOrEqual : Float → Float → Set
FloatGreaterOrEqual x y =
  FloatLessOrEqual y x

zeroFloat : Float
zeroFloat = primNatToFloat zero

All : {A : Set} → (A → Set) → List A → Set
All predicate [] = Top
All predicate (x ∷ xs) =
  predicate x ∧ All predicate xs

Pairwise :
  {A : Set} →
  (A → A → Set) →
  List A →
  Set
Pairwise relation [] = Top
Pairwise relation (x ∷ xs) =
  All (relation x) xs ∧ Pairwise relation xs

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

absDiff : Float → Float → Float
absDiff a b =
  let difference = primFloatMinus a b
  in
    if primFloatLess difference zeroFloat
    then primFloatMinus b a
    else difference

FiniteFloat : Float → Set
FiniteFloat x =
  IsFalse (primFloatIsNaN x) ∧
  IsFalse (primFloatIsInfinite x)

has-close-elements-precond :
  List Float →
  Float →
  Set
has-close-elements-precond numbers threshold =
  FloatGreaterOrEqual threshold zeroFloat ∧
  IsFalse (primFloatIsNaN threshold) ∧
  All FiniteFloat numbers

hasCloseWith :
  List Float →
  Float →
  Float →
  Bool
hasCloseWith [] current threshold = false
hasCloseWith (earlier ∷ rest) current threshold =
  if primFloatLess (absDiff earlier current) threshold
  then true
  else hasCloseWith rest current threshold

hasCloseElementsLoop :
  List Float →
  List Float →
  Float →
  Bool
hasCloseElementsLoop earlier [] threshold = false
hasCloseElementsLoop earlier (current ∷ later) threshold =
  if hasCloseWith earlier current threshold
  then true
  else
    hasCloseElementsLoop
      (earlier ++ (current ∷ []))
      later
      threshold

has-close-elements :
  (numbers : List Float) →
  (threshold : Float) →
  has-close-elements-precond numbers threshold →
  Bool
has-close-elements numbers threshold h-precond =
  hasCloseElementsLoop [] numbers threshold

has-close-elements-postcond :
  (numbers : List Float) →
  (threshold : Float) →
  (result : Bool) →
  has-close-elements-precond numbers threshold →
  Set
has-close-elements-postcond
  numbers
  threshold
  result
  h-precond =
  Not (IsTrue result) ↔
  Pairwise
    (λ a b →
      FloatGreaterOrEqual
        (absDiff a b)
        threshold)
    numbers

has-close-elements-spec-satisfied : Set
has-close-elements-spec-satisfied =
  (numbers : List Float) →
  (threshold : Float) →
  (h-precond :
    has-close-elements-precond numbers threshold) →
  has-close-elements-postcond
    numbers
    threshold
    (has-close-elements
      numbers
      threshold
      h-precond)
    h-precond
