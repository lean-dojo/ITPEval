-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/patience_PatienceCode_push_cardqtvc: the push-card verification
-- condition for preserving nonempty integer-valued patience-solitaire stacks.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module patience_PatienceCode_push_cardqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≤Z_
infixr 3 _∧_

data ⊥ : Set where

record ⊤ : Set where
  constructor tt

Not : Set → Set
Not A = A → ⊥

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

_≤Z_ : Int → Int → Set
x ≤Z y = intLessOrEqual x y ≡ true

reverseAppend : {A : Set} → List A → List A → List A
reverseAppend [] ys = ys
reverseAppend (x ∷ xs) ys = reverseAppend xs (x ∷ ys)

wfStacks : List (List Int) → Set
wfStacks [] = ⊤
wfStacks ([] ∷ remaining) = ⊥
wfStacks ((_ ∷ _) ∷ remaining) = wfStacks remaining

TailMatches : List (List Int) → List (List Int) → Set
TailMatches [] remaining = ⊥
TailMatches (_ ∷ tail) remaining = tail ≡ remaining

RecursiveSideCondition :
  List (List Int) →
  List (List Int) →
  Int →
  Set
RecursiveSideCondition [] acc c = ⊤
RecursiveSideCondition ([] ∷ remaining) acc c = ⊥
RecursiveSideCondition ((c′ ∷ cards) ∷ remaining) acc c =
  Not (c ≤Z c′) →
  TailMatches ((c′ ∷ cards) ∷ remaining) remaining
  ∧ wfStacks remaining
  ∧ wfStacks ((c′ ∷ cards) ∷ acc)

ResultPremise :
  List (List Int) →
  List (List Int) →
  Int →
  List (List Int) →
  Set
ResultPremise [] acc c result =
  result ≡ reverseAppend ((c ∷ []) ∷ acc) []
ResultPremise ([] ∷ remaining) acc c result = ⊥
ResultPremise ((c′ ∷ cards) ∷ remaining) acc c result =
  IfSet
    (intLessOrEqual c c′)
    (result ≡
      reverseAppend ((c ∷ c′ ∷ cards) ∷ acc) remaining)
    (wfStacks result)

push-card'vc : Set
push-card'vc =
  (stacks1 acc : List (List Int)) →
  (c : Int) →
  wfStacks stacks1 →
  wfStacks acc →
  RecursiveSideCondition stacks1 acc c
  ∧
  ((result : List (List Int)) →
    ResultPremise stacks1 acc c result →
    wfStacks result)
