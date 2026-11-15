-- Statement-only formalization of VERINA corpus artifact verina_basic_13,
-- catalog title "cubeElements": a deterministic integer-array program maps
-- each element to its cube and is connected to its size-and-indexed-value
-- correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic13 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _≤_ _<_
infixl 7 _*z_
infixr 3 _∧_

record Top : Set where
  constructor top

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

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

_*z_ : Int → Int → Int
pos m *z pos n = pos (m * n)
pos m *z negsuc n = negative (m * suc n)
negsuc m *z pos n = negative (suc m * n)
negsuc m *z negsuc n = pos (suc m * suc n)

zeroInt : Int
zeroInt = pos zero

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

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

cubeInt : Int → Int
cubeInt x = (x *z x) *z x

cubeElements-precond : Array Int → Set
cubeElements-precond a = Top

cubeElements :
  (a : Array Int) →
  cubeElements-precond a →
  Array Int
cubeElements a h-precond =
  mapList cubeInt a

cubeElements-postcond :
  (a : Array Int) →
  (result : Array Int) →
  cubeElements-precond a →
  Set
cubeElements-postcond a result h-precond =
  (arraySize result ≡ arraySize a) ∧
  ((i : Nat) →
    i < arraySize a →
    indexDefault zeroInt result i ≡
      cubeInt (indexDefault zeroInt a i))

cubeElements-spec-satisfied : Set
cubeElements-spec-satisfied =
  (a : Array Int) →
  (h-precond : cubeElements-precond a) →
  cubeElements-postcond
    a
    (cubeElements a h-precond)
    h-precond
