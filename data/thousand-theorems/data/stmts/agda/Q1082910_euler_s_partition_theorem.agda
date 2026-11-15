-- Statement-only formalization of thousand-theorems corpus artifact Q1082910,
-- "Euler's partition theorem": for every natural number, the finite numbers
-- of partitions into odd positive parts and into distinct positive parts are
-- equal. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1082910_euler_s_partition_theorem where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infixr 5 _++_
infixr 6 _and_

_++_ :
  {A : Set} →
  List A →
  List A →
  List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map :
  {A B : Set} →
  (A → B) →
  List A →
  List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

concat :
  {A : Set} →
  List (List A) →
  List A
concat [] = []
concat (xs ∷ xss) = xs ++ concat xss

concatMap :
  {A B : Set} →
  (A → List B) →
  List A →
  List B
concatMap f xs = concat (map f xs)

_and_ :
  Bool →
  Bool →
  Bool
true and right = right
false and right = false

equalNat :
  Nat →
  Nat →
  Bool
equalNat zero zero = true
equalNat zero (suc right) = false
equalNat (suc left) zero = false
equalNat (suc left) (suc right) = equalNat left right

lessEqual :
  Nat →
  Nat →
  Bool
lessEqual zero right = true
lessEqual (suc left) zero = false
lessEqual (suc left) (suc right) = lessEqual left right

lessThan :
  Nat →
  Nat →
  Bool
lessThan left right = lessEqual (suc left) right

positive :
  Nat →
  Bool
positive zero = false
positive (suc n) = true

odd :
  Nat →
  Bool
odd zero = false
odd (suc zero) = true
odd (suc (suc n)) = odd n

all :
  (Nat → Bool) →
  List Nat →
  Bool
all predicate [] = true
all predicate (x ∷ xs) =
  predicate x and all predicate xs

sum :
  List Nat →
  Nat
sum [] = zero
sum (x ∷ xs) = x + sum xs

nonIncreasing :
  List Nat →
  Bool
nonIncreasing [] = true
nonIncreasing (x ∷ []) = true
nonIncreasing (x ∷ y ∷ xs) =
  lessEqual y x and nonIncreasing (y ∷ xs)

strictlyDecreasing :
  List Nat →
  Bool
strictlyDecreasing [] = true
strictlyDecreasing (x ∷ []) = true
strictlyDecreasing (x ∷ y ∷ xs) =
  lessThan y x and strictlyDecreasing (y ∷ xs)

positivePartsUpTo :
  Nat →
  List Nat
positivePartsUpTo zero = []
positivePartsUpTo (suc n) =
  suc n ∷ positivePartsUpTo n

listsOfLength :
  Nat →
  List Nat →
  List (List Nat)
listsOfLength zero alphabet = [] ∷ []
listsOfLength (suc length) alphabet =
  concatMap
    (λ head →
      map
        (λ tail → head ∷ tail)
        (listsOfLength length alphabet))
    alphabet

listsUpToLength :
  Nat →
  List Nat →
  List (List Nat)
listsUpToLength zero alphabet = [] ∷ []
listsUpToLength (suc bound) alphabet =
  listsUpToLength bound alphabet ++
  listsOfLength (suc bound) alphabet

partitionCandidates :
  Nat →
  List (List Nat)
partitionCandidates n =
  listsUpToLength n (positivePartsUpTo n)

isOddPartition :
  Nat →
  List Nat →
  Bool
isOddPartition n parts =
  equalNat (sum parts) n and
  (all positive parts and
   (nonIncreasing parts and all odd parts))

isDistinctPartition :
  Nat →
  List Nat →
  Bool
isDistinctPartition n parts =
  equalNat (sum parts) n and
  (all positive parts and strictlyDecreasing parts)

countSatisfying :
  (List Nat → Bool) →
  List (List Nat) →
  Nat
countSatisfying predicate [] = zero
countSatisfying predicate (parts ∷ rest)
  with predicate parts
... | true = suc (countSatisfying predicate rest)
... | false = countSatisfying predicate rest

oddPartitionCount :
  Nat →
  Nat
oddPartitionCount n =
  countSatisfying
    (isOddPartition n)
    (partitionCandidates n)

distinctPartitionCount :
  Nat →
  Nat
distinctPartitionCount n =
  countSatisfying
    (isDistinctPartition n)
    (partitionCandidates n)

euler-partition-theorem : Set
euler-partition-theorem =
  (n : Nat) →
  oddPartitionCount n ≡ distinctPartitionCount n
