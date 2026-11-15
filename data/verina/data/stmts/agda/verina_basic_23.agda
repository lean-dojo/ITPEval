-- Statement-only formalization of VERINA corpus artifact verina_basic_23,
-- catalog title "differenceMinMax": a deterministic nonempty integer-array
-- scan returns the maximum minus the minimum and is connected to the fold-based
-- minimum/maximum correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic23 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

intSuccessor : Int → Int
intSuccessor (pos n) = pos (suc n)
intSuccessor (negsuc zero) = pos zero
intSuccessor (negsuc (suc n)) = negsuc n

intPredecessor : Int → Int
intPredecessor (pos zero) = negsuc zero
intPredecessor (pos (suc n)) = pos n
intPredecessor (negsuc n) = negsuc (suc n)

intAdd : Int → Int → Int
intAdd x (pos zero) = x
intAdd x (pos (suc n)) =
  intSuccessor (intAdd x (pos n))
intAdd x (negsuc zero) = intPredecessor x
intAdd x (negsuc (suc n)) =
  intPredecessor (intAdd x (negsuc n))

intNegate : Int → Int
intNegate (pos zero) = pos zero
intNegate (pos (suc n)) = negsuc n
intNegate (negsuc n) = pos (suc n)

intSubtract : Int → Int → Int
intSubtract x y = intAdd x (intNegate y)

zeroInt : Int
zeroInt = pos zero

Array : Set → Set
Array A = List A

data NonEmpty {A : Set} : List A → Set where
  nonempty : {x : A} {xs : List A} → NonEmpty (x ∷ xs)

headDefault : {A : Set} → A → List A → A
headDefault default [] = default
headDefault default (x ∷ xs) = x

foldLeft : {A B : Set} → (A → B → A) → A → List B → A
foldLeft step accumulator [] = accumulator
foldLeft step accumulator (x ∷ xs) =
  foldLeft step (step accumulator x) xs

minimumStep : Int → Int → Int
minimumStep accumulator x =
  if intLess x accumulator
  then x
  else accumulator

maximumStep : Int → Int → Int
maximumStep accumulator x =
  if intLess accumulator x
  then x
  else accumulator

differenceMinMax-loop : List Int → Int → Int → Int
differenceMinMax-loop [] minimum maximum =
  intSubtract maximum minimum
differenceMinMax-loop (x ∷ xs) minimum maximum =
  differenceMinMax-loop
    xs
    (minimumStep minimum x)
    (maximumStep maximum x)

differenceMinMax-precond : Array Int → Set
differenceMinMax-precond a = NonEmpty a

differenceMinMax :
  (a : Array Int) →
  differenceMinMax-precond a →
  Int
differenceMinMax [] ()
differenceMinMax (x ∷ xs) nonempty =
  differenceMinMax-loop xs x x

differenceMinMax-postcond :
  (a : Array Int) →
  (result : Int) →
  differenceMinMax-precond a →
  Set
differenceMinMax-postcond a result h-precond =
  intAdd
    result
    (foldLeft
      minimumStep
      (headDefault zeroInt a)
      a)
  ≡
  foldLeft
    maximumStep
    (headDefault zeroInt a)
    a

differenceMinMax-spec-satisfied : Set
differenceMinMax-spec-satisfied =
  (a : Array Int) →
  (h-precond : differenceMinMax-precond a) →
  differenceMinMax-postcond
    a
    (differenceMinMax a h-precond)
    h-precond
