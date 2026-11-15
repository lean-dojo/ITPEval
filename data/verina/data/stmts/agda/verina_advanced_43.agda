-- Statement-only formalization of VERINA corpus artifact verina_advanced_43,
-- catalog title "maxStrength": a deterministic bitmask program computes the
-- maximum product of a nonempty subset of an integer list and is connected to
-- its full maximality contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced43 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infixr 3 _∧_

data Empty : Set where

Not : Set → Set
Not A = A → Empty

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

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natHalf : Nat → Nat
natHalf zero = zero
natHalf (suc zero) = zero
natHalf (suc (suc n)) = suc (natHalf n)

natOdd : Nat → Bool
natOdd zero = false
natOdd (suc zero) = true
natOdd (suc (suc n)) = natOdd n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

intLessOrEqual : Int → Int → Bool
intLessOrEqual x y =
  if intLess y x
  then false
  else true

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

intMultiply : Int → Int → Int
intMultiply (pos m) (pos n) = pos (m * n)
intMultiply (pos m) (negsuc n) = negative (m * suc n)
intMultiply (negsuc m) (pos n) = negative (suc m * n)
intMultiply (negsuc m) (negsuc n) = pos (suc m * suc n)

intMax : Int → Int → Int
intMax x y =
  if intLess x y
  then y
  else x

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

appendList : {A : Set} → List A → List A → List A
appendList [] ys = ys
appendList (x ∷ xs) ys = x ∷ appendList xs ys

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

filterList : {A : Set} → (A → Bool) → List A → List A
filterList predicate [] = []
filterList predicate (x ∷ xs) =
  if predicate x
  then x ∷ filterList predicate xs
  else filterList predicate xs

foldLeft : {A B : Set} → (A → B → A) → A → List B → A
foldLeft step accumulator [] = accumulator
foldLeft step accumulator (x ∷ xs) =
  foldLeft step (step accumulator x) xs

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc count) =
  start ∷ rangeFrom (suc start) count

range : Nat → List Nat
range count = rangeFrom zero count

two : Nat
two = suc (suc zero)

powTwo : Nat → Nat
powTwo zero = suc zero
powTwo (suc n) = two * powTwo n

selectByMask : List Int → Nat → List Int
selectByMask [] mask = []
selectByMask (x ∷ xs) mask =
  if natOdd mask
  then x ∷ selectByMask xs (natHalf mask)
  else selectByMask xs (natHalf mask)

powerSetByMasks : List Int → List (List Int)
powerSetByMasks nums =
  mapList
    (selectByMask nums)
    (range (powTwo (listLength nums)))

listNonEmpty : {A : Set} → List A → Bool
listNonEmpty [] = false
listNonEmpty (_ ∷ _) = true

oneInt : Int
oneInt = pos (suc zero)

productList : List Int → Int
productList xs = foldLeft intMultiply oneInt xs

maximumWithDefault : Int → List Int → Int
maximumWithDefault default [] = default
maximumWithDefault default (x ∷ xs) =
  foldLeft intMax x xs

minusOneMillion : Int
minusOneMillion = negsuc 999999

maxStrength-precond : List Int → Set
maxStrength-precond nums = Not (nums ≡ [])

maxStrength :
  (nums : List Int) →
  maxStrength-precond nums →
  Int
maxStrength nums h-precond =
  let subsets = powerSetByMasks nums
      nonempty = filterList listNonEmpty subsets
      products = mapList productList nonempty
  in maximumWithDefault minusOneMillion products

allSublists : List Int → List (List Int)
allSublists [] = [] ∷ []
allSublists (x ∷ xs) =
  let tails = allSublists xs
  in
    appendList
      tails
      (mapList (λ tail → x ∷ tail) tails)

containsInt : Int → List Int → Bool
containsInt sought [] = false
containsInt sought (x ∷ xs) =
  if intEqual sought x
  then true
  else containsInt sought xs

maxStrength-postcond :
  (nums : List Int) →
  (result : Int) →
  maxStrength-precond nums →
  Set
maxStrength-postcond nums result h-precond =
  let sublists =
        filterList listNonEmpty (allSublists nums)
      products =
        mapList productList sublists
  in
    IsTrue (containsInt result products) ∧
    IsTrue
      (allList
        (λ product → intLessOrEqual product result)
        products)

maxStrength-spec-satisfied : Set
maxStrength-spec-satisfied =
  (nums : List Int) →
  (h-precond : maxStrength-precond nums) →
  maxStrength-postcond
    nums
    (maxStrength nums h-precond)
    h-precond
