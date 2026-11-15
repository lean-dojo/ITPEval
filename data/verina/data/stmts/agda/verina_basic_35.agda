-- Statement-only formalization of VERINA corpus artifact verina_basic_35,
-- catalog title "MoveZeroesToEnd": a deterministic integer-array program
-- stably moves all zeroes to the end and is connected to its permutation and
-- first-zero prefix/suffix correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic35 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

boolNot : Bool → Bool
boolNot true = false
boolNot false = true

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

zeroInt : Int
zeroInt = pos zero

Array : Set → Set
Array A = List A

appendList : {A : Set} → List A → List A → List A
appendList [] ys = ys
appendList (x ∷ xs) ys = x ∷ appendList xs ys

filterList : {A : Set} → (A → Bool) → List A → List A
filterList predicate [] = []
filterList predicate (x ∷ xs) =
  if predicate x
  then x ∷ filterList predicate xs
  else filterList predicate xs

takeList : {A : Set} → Nat → List A → List A
takeList zero xs = []
takeList (suc n) [] = []
takeList (suc n) (x ∷ xs) =
  x ∷ takeList n xs

dropList : {A : Set} → Nat → List A → List A
dropList zero xs = xs
dropList (suc n) [] = []
dropList (suc n) (_ ∷ xs) = dropList n xs

idxOfInt : Int → List Int → Nat
idxOfInt sought [] = zero
idxOfInt sought (x ∷ xs) =
  if intEqual sought x
  then zero
  else suc (idxOfInt sought xs)

data Permutation {A : Set} : List A → List A → Set where
  permutationNil :
    Permutation [] []

  permutationSkip :
    {x : A} {xs ys : List A} →
    Permutation xs ys →
    Permutation (x ∷ xs) (x ∷ ys)

  permutationSwap :
    {x y : A} {xs : List A} →
    Permutation (y ∷ x ∷ xs) (x ∷ y ∷ xs)

  permutationTrans :
    {xs ys zs : List A} →
    Permutation xs ys →
    Permutation ys zs →
    Permutation xs zs

MoveZeroesToEnd-precond : Array Int → Set
MoveZeroesToEnd-precond arr = Top

MoveZeroesToEnd :
  (arr : Array Int) →
  MoveZeroesToEnd-precond arr →
  Array Int
MoveZeroesToEnd arr h-precond =
  let nonZeros =
        filterList
          (λ x → boolNot (intEqual x zeroInt))
          arr
      zeros =
        filterList
          (λ x → intEqual x zeroInt)
          arr
  in appendList nonZeros zeros

MoveZeroesToEnd-postcond :
  (arr : Array Int) →
  (result : Array Int) →
  MoveZeroesToEnd-precond arr →
  Set
MoveZeroesToEnd-postcond arr result h-precond =
  let firstResZeroIdx = idxOfInt zeroInt result
  in
    Permutation result arr ∧
    (takeList firstResZeroIdx result ≡
      filterList
        (λ x → boolNot (intEqual x zeroInt))
        arr) ∧
    (dropList firstResZeroIdx result ≡
      filterList
        (λ x → intEqual x zeroInt)
        arr)

MoveZeroesToEnd-spec-satisfied : Set
MoveZeroesToEnd-spec-satisfied =
  (arr : Array Int) →
  (h-precond : MoveZeroesToEnd-precond arr) →
  MoveZeroesToEnd-postcond
    arr
    (MoveZeroesToEnd arr h-precond)
    h-precond
