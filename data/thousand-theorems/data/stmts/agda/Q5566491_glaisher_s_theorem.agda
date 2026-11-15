-- Statement-only formalization of thousand-theorems corpus artifact Q5566491,
-- "Glaisher's theorem": for every natural n and positive m, the number of
-- partitions of n into positive parts not divisible by m equals the number
-- in which every positive part occurs fewer than m times. This file contains no proof.

{-# OPTIONS --safe #-}

module Q5566491_glaisher_s_theorem where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 5 _++_
infixr 6 _and_

data IsTrue : Bool → Set where
  true-witness : IsTrue true

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

notBool :
  Bool →
  Bool
notBool true = false
notBool false = true

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

any :
  (Nat → Bool) →
  List Nat →
  Bool
any predicate [] = false
any predicate (x ∷ xs) with predicate x
... | true = true
... | false = any predicate xs

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

naturalsThrough :
  Nat →
  List Nat
naturalsThrough zero = zero ∷ []
naturalsThrough (suc n) =
  suc n ∷ naturalsThrough n

divides :
  Nat →
  Nat →
  Bool
divides divisor value =
  any
    (λ factor → equalNat (divisor * factor) value)
    (naturalsThrough value)

countOccurrences :
  Nat →
  List Nat →
  Nat
countOccurrences value [] = zero
countOccurrences value (x ∷ xs) with equalNat value x
... | true = suc (countOccurrences value xs)
... | false = countOccurrences value xs

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

isNonDivisiblePartition :
  Nat →
  Nat →
  List Nat →
  Bool
isNonDivisiblePartition n m parts =
  equalNat (sum parts) n and
  (all positive parts and
   (nonIncreasing parts and
    all (λ part → notBool (divides m part)) parts))

multiplicitiesBelow :
  Nat →
  Nat →
  List Nat →
  Bool
multiplicitiesBelow n m parts =
  all
    (λ part → lessThan (countOccurrences part parts) m)
    (positivePartsUpTo n)

isMultiplicityRestrictedPartition :
  Nat →
  Nat →
  List Nat →
  Bool
isMultiplicityRestrictedPartition n m parts =
  equalNat (sum parts) n and
  (all positive parts and
   (nonIncreasing parts and multiplicitiesBelow n m parts))

countSatisfying :
  (List Nat → Bool) →
  List (List Nat) →
  Nat
countSatisfying predicate [] = zero
countSatisfying predicate (parts ∷ rest) with predicate parts
... | true = suc (countSatisfying predicate rest)
... | false = countSatisfying predicate rest

nonDivisiblePartitionCount :
  Nat →
  Nat →
  Nat
nonDivisiblePartitionCount n m =
  countSatisfying
    (isNonDivisiblePartition n m)
    (partitionCandidates n)

multiplicityRestrictedPartitionCount :
  Nat →
  Nat →
  Nat
multiplicityRestrictedPartitionCount n m =
  countSatisfying
    (isMultiplicityRestrictedPartition n m)
    (partitionCandidates n)

glaisher-s-theorem : Set
glaisher-s-theorem =
  (n m : Nat) →
  IsTrue (positive m) →
  nonDivisiblePartitionCount n m ≡
  multiplicityRestrictedPartitionCount n m
