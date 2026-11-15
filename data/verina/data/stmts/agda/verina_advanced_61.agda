-- Statement-only formalization of VERINA corpus artifact verina_advanced_61,
-- catalog title "productExceptSelf": a deterministic prefix-and-suffix product
-- program returns, at each integer-list index, the product of all other entries
-- and is connected to its pointwise correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced61 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infixr 3 _∧_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data IsTrue : Bool → Set where
  true-witness : IsTrue true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

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

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

intMultiply : Int → Int → Int
intMultiply (pos m) (pos n) = pos (m * n)
intMultiply (pos m) (negsuc n) = negative (m * suc n)
intMultiply (negsuc m) (pos n) = negative (suc m * n)
intMultiply (negsuc m) (negsuc n) = pos (suc m * suc n)

zeroInt : Int
zeroInt = pos zero

oneInt : Int
oneInt = pos (suc zero)

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

appendList : {A : Set} → List A → List A → List A
appendList [] ys = ys
appendList (x ∷ xs) ys = x ∷ appendList xs ys

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

foldLeft : {A B : Set} → (A → B → A) → A → List B → A
foldLeft step accumulator [] = accumulator
foldLeft step accumulator (x ∷ xs) =
  foldLeft step (step accumulator x) xs

reverseOnto : {A : Set} → List A → List A → List A
reverseOnto accumulator [] = accumulator
reverseOnto accumulator (x ∷ xs) =
  reverseOnto (x ∷ accumulator) xs

reverseList : {A : Set} → List A → List A
reverseList xs = reverseOnto [] xs

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

takeList : {A : Set} → Nat → List A → List A
takeList zero xs = []
takeList (suc n) [] = []
takeList (suc n) (x ∷ xs) =
  x ∷ takeList n xs

dropList : {A : Set} → Nat → List A → List A
dropList zero xs = xs
dropList (suc n) [] = []
dropList (suc n) (_ ∷ xs) =
  dropList n xs

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc count) =
  start ∷ rangeFrom (suc start) count

range : Nat → List Nat
range count = rangeFrom zero count

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

getLastDefault : {A : Set} → A → List A → A
getLastDefault default [] = default
getLastDefault default (x ∷ []) = x
getLastDefault default (x ∷ y ∷ ys) =
  getLastDefault default (y ∷ ys)

prefixStep : List Int → Int → List Int
prefixStep accumulator x =
  appendList
    accumulator
    (intMultiply
      (getLastDefault zeroInt accumulator)
      x ∷ [])

computepref : List Int → List Int
computepref nums =
  foldLeft prefixStep (oneInt ∷ []) nums

computeSuffix : List Int → List Int
computeSuffix nums =
  reverseList
    (foldLeft
      prefixStep
      (oneInt ∷ [])
      (reverseList nums))

productExceptSelf-precond : List Int → Set
productExceptSelf-precond nums = Top

productExceptSelf :
  (nums : List Int) →
  productExceptSelf-precond nums →
  List Int
productExceptSelf nums h-precond with listLength nums
... | zero = []
... | suc n =
  let pref = computepref nums
      suffix = computeSuffix nums
  in
    mapList
      (λ i →
        intMultiply
          (nthDefault zeroInt i pref)
          (nthDefault zeroInt (suc i) suffix))
      (range (suc n))

productList : List Int → Int
productList [] = oneInt
productList (x ∷ xs) =
  intMultiply x (productList xs)

productExceptSelf-postcond :
  (nums : List Int) →
  (result : List Int) →
  productExceptSelf-precond nums →
  Set
productExceptSelf-postcond nums result h-precond =
  (listLength nums ≡ listLength result) ∧
  IsTrue
    (allList
      (λ i →
        intEqual
          (nthDefault zeroInt i result)
          (intMultiply
            (productList (takeList i nums))
            (productList (dropList (suc i) nums))))
      (range (listLength nums)))

productExceptSelf-spec-satisfied : Set
productExceptSelf-spec-satisfied =
  (nums : List Int) →
  (h-precond : productExceptSelf-precond nums) →
  productExceptSelf-postcond
    nums
    (productExceptSelf nums h-precond)
    h-precond
