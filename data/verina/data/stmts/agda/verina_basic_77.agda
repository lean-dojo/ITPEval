-- Statement-only formalization of VERINA corpus artifact verina_basic_77,
-- catalog title "modify_array_element": a deterministic nested-array update
-- replaces one selected natural-number element and is connected to its
-- structure-preserving correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic77 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infix 4 _≠_ _≤_ _<_

data Empty : Set where

Not : Set → Set
Not proposition = proposition → Empty

_≠_ : {A : Set} → A → A → Set
x ≠ y = Not (x ≡ y)

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

Array : Set → Set
Array A = List A

arraySize : {A : Set} → Array A → Nat
arraySize [] = zero
arraySize (_ ∷ xs) = suc (arraySize xs)

indexDefault : {A : Set} → A → Array A → Nat → A
indexDefault default [] index = default
indexDefault default (x ∷ xs) zero = x
indexDefault default (x ∷ xs) (suc index) =
  indexDefault default xs index

updateAt : {A : Set} → Array A → Nat → A → Array A
updateAt [] index value = []
updateAt (x ∷ xs) zero value = value ∷ xs
updateAt (x ∷ xs) (suc index) value =
  x ∷ updateAt xs index value

modify-array-element-precond :
  Array (Array Nat) →
  Nat →
  Nat →
  Nat →
  Set
modify-array-element-precond arr index1 index2 val =
  (index1 < arraySize arr) ∧
  (index2 < arraySize (indexDefault [] arr index1))

updateInner : Array Nat → Nat → Nat → Array Nat
updateInner a index value = updateAt a index value

modify-array-element :
  (arr : Array (Array Nat)) →
  (index1 index2 val : Nat) →
  modify-array-element-precond arr index1 index2 val →
  Array (Array Nat)
modify-array-element arr index1 index2 val h-precond =
  let inner = indexDefault [] arr index1
      inner-updated = updateInner inner index2 val
  in updateAt arr index1 inner-updated

modify-array-element-postcond :
  (arr : Array (Array Nat)) →
  (index1 index2 val : Nat) →
  (result : Array (Array Nat)) →
  modify-array-element-precond arr index1 index2 val →
  Set
modify-array-element-postcond
  arr
  index1
  index2
  val
  result
  h-precond =
    (arraySize result ≡ arraySize arr) ∧
    (arraySize (indexDefault [] result index1) ≡
      arraySize (indexDefault [] arr index1)) ∧
    ((i : Nat) →
      i < arraySize arr →
      i ≠ index1 →
      indexDefault [] result i ≡ indexDefault [] arr i) ∧
    ((j : Nat) →
      j < arraySize (indexDefault [] arr index1) →
      j ≠ index2 →
      indexDefault
        zero
        (indexDefault [] result index1)
        j
      ≡
      indexDefault
        zero
        (indexDefault [] arr index1)
        j) ∧
    (indexDefault
      zero
      (indexDefault [] result index1)
      index2
    ≡ val)

modify-array-element-spec-satisfied : Set
modify-array-element-spec-satisfied =
  (arr : Array (Array Nat)) →
  (index1 index2 val : Nat) →
  (h-precond :
    modify-array-element-precond arr index1 index2 val) →
  modify-array-element-postcond
    arr
    index1
    index2
    val
    (modify-array-element
      arr
      index1
      index2
      val
      h-precond)
    h-precond
