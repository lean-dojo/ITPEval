-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2019_ghc_sort_Top_orderqtvc: ordering a strictly increasing
-- or nonincreasing integer list by retaining it or reversing it, with a
-- nondecreasing permutation as the result. This file contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2019GhcSortTopOrderVC where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_
infixr 2 _∨_

data ⊤ : Set where
  tt : ⊤

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

_≤Z_ : Int → Int → Set
x ≤Z y = intLessOrEqual x y ≡ true

_<Z_ : Int → Int → Set
x <Z y = intLess x y ≡ true

reverseAcc : {A : Set} → List A → List A → List A
reverseAcc [] accumulator = accumulator
reverseAcc (x ∷ xs) accumulator = reverseAcc xs (x ∷ accumulator)

reverse : {A : Set} → List A → List A
reverse xs = reverseAcc xs []

data StrictlyIncreasing : List Int → Set where
  strictlyIncreasingNil :
    StrictlyIncreasing []

  strictlyIncreasingOne :
    (x : Int) →
    StrictlyIncreasing (x ∷ [])

  strictlyIncreasingTwo :
    (x y : Int) →
    (tail : List Int) →
    x <Z y →
    StrictlyIncreasing (y ∷ tail) →
    StrictlyIncreasing (x ∷ y ∷ tail)

data Nondecreasing : List Int → Set where
  nondecreasingNil :
    Nondecreasing []

  nondecreasingOne :
    (x : Int) →
    Nondecreasing (x ∷ [])

  nondecreasingTwo :
    (x y : Int) →
    (tail : List Int) →
    x ≤Z y →
    Nondecreasing (y ∷ tail) →
    Nondecreasing (x ∷ y ∷ tail)

data Nonincreasing : List Int → Set where
  nonincreasingNil :
    Nonincreasing []

  nonincreasingOne :
    (x : Int) →
    Nonincreasing (x ∷ [])

  nonincreasingTwo :
    (x y : Int) →
    (tail : List Int) →
    y ≤Z x →
    Nonincreasing (y ∷ tail) →
    Nonincreasing (x ∷ y ∷ tail)

data Perm {A : Set} : List A → List A → Set where
  permNil :
    Perm [] []

  permKeep :
    {x : A} {xs ys : List A} →
    Perm xs ys →
    Perm (x ∷ xs) (x ∷ ys)

  permSwap :
    (x y : A) →
    (xs : List A) →
    Perm (x ∷ y ∷ xs) (y ∷ x ∷ xs)

  permTrans :
    {xs ys zs : List A} →
    Perm xs ys →
    Perm ys zs →
    Perm xs zs

ShapeCondition : List Int → Set
ShapeCondition [] = ⊤
ShapeCondition (_ ∷ []) = ⊤
ShapeCondition (_ ∷ _ ∷ _) = ⊤

OrderResult : List Int → List Int → Set
OrderResult [] result = result ≡ []
OrderResult (x ∷ []) result = result ≡ (x ∷ [])
OrderResult (h₁ ∷ h₂ ∷ tail) result with intLess h₁ h₂
... | true = result ≡ (h₁ ∷ h₂ ∷ tail)
... | false = result ≡ reverse (h₁ ∷ h₂ ∷ tail)

OrderGoal : List Int → Set
OrderGoal input =
  ShapeCondition input ∧
  ((result : List Int) →
    OrderResult input result →
    Nondecreasing result ∧ Perm input result)

order'vc : Set
order'vc =
  (input : List Int) →
  StrictlyIncreasing input ∨ Nonincreasing input →
  OrderGoal input
