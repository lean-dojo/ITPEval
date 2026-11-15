-- Statement-only formalization of VERINA corpus artifact verina_advanced_44,
-- catalog title "maxSubarraySumDivisibleByK": a deterministic prefix-sum
-- program computes the maximum sum of a nonempty contiguous integer subarray
-- whose length is divisible by k, with its full contract. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced44 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; div-helper; mod-helper)

infixr 3 _∧_
infixr 5 _&&_ _||_
infix 4 _≤_ _<_
infix 4 _∈_

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

data IsTrue : Bool → Set where
  true-witness : IsTrue true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

_&&_ : Bool → Bool → Bool
true && other = other
false && other = false

_||_ : Bool → Bool → Bool
true || other = true
false || other = other

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

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

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

intMax : Int → Int → Int
intMax x y =
  if intLess x y
  then y
  else x

intNatAbs : Int → Nat
intNatAbs (pos n) = n
intNatAbs (negsuc n) = suc n

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc n) = zero

listIsEmpty : {A : Set} → List A → Bool
listIsEmpty [] = true
listIsEmpty (_ ∷ _) = false

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

appendList : {A : Set} → List A → List A → List A
appendList [] ys = ys
appendList (x ∷ xs) ys = x ∷ appendList xs ys

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

flatMapList : {A B : Set} → (A → List B) → List A → List B
flatMapList f [] = []
flatMapList f (x ∷ xs) =
  appendList (f x) (flatMapList f xs)

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

takeList : {A : Set} → Nat → List A → List A
takeList zero xs = []
takeList (suc n) [] = []
takeList (suc n) (x ∷ xs) =
  x ∷ takeList n xs

dropList : {A : Set} → Nat → List A → List A
dropList zero xs = xs
dropList (suc n) [] = []
dropList (suc n) (_ ∷ xs) = dropList n xs

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc count) =
  start ∷ rangeFrom (suc start) count

range : Nat → List Nat
range count = rangeFrom zero count

sumList : List Int → Int
sumList xs = foldLeft intAdd (pos zero) xs

data PositiveInt : Int → Set where
  positive-int : {n : Nat} → PositiveInt (pos (suc n))

maxSubarraySumDivisibleByK-precond :
  List Int →
  Int →
  Set
maxSubarraySumDivisibleByK-precond arr k =
  PositiveInt k

prefixSumsFrom : Int → List Int → List Int
prefixSumsFrom accumulator [] =
  accumulator ∷ []
prefixSumsFrom accumulator (x ∷ xs) =
  accumulator ∷
  prefixSumsFrom (intAdd accumulator x) xs

prefixSums : List Int → List Int
prefixSums arr = prefixSumsFrom (pos zero) arr

lengthDivisibleByInt : Nat → Int → Bool
lengthDivisibleByInt length k =
  natEqual
    (naturalMod length (intNatAbs k))
    zero

updateBest : Maybe Int → Int → Maybe Int
updateBest nothing value = just value
updateBest (just best) value =
  just (intMax best value)

processStart :
  List Int →
  Nat →
  Maybe Int →
  Nat →
  Maybe Int
processStart sums length best start =
  let finish = start + length
      subarray-sum =
        intSubtract
          (nthDefault (pos zero) finish sums)
          (nthDefault (pos zero) start sums)
  in updateBest best subarray-sum

processLength :
  Nat →
  List Int →
  Int →
  Maybe Int →
  Nat →
  Maybe Int
processLength n sums k best length =
  if
    lengthDivisibleByInt length k &&
    natLess zero length
  then
    foldLeft
      (processStart sums length)
      best
      (range (suc (natSubtract n length)))
  else best

maybeIntOrZero : Maybe Int → Int
maybeIntOrZero nothing = pos zero
maybeIntOrZero (just value) = value

maxSubarraySumDivisibleByK :
  List Int →
  Int →
  Int
maxSubarraySumDivisibleByK arr k =
  let n = listLength arr
  in
    if
      listIsEmpty arr ||
      intEqual k (pos zero)
    then pos zero
    else
      maybeIntOrZero
        (foldLeft
          (processLength n (prefixSums arr) k)
          nothing
          (range (suc n)))

allSubarrays : List Int → List (List Int)
allSubarrays arr =
  let n = listLength arr
  in
    flatMapList
      (λ start →
        mapList
          (λ length →
            takeList length (dropList start arr))
          (range (suc (natSubtract n start))))
      (range n)

subarrayLengthDivisibleByNat : Nat → List Int → Bool
subarrayLengthDivisibleByNat divisor subarray =
  natEqual
    (naturalMod (listLength subarray) divisor)
    zero &&
  natLess zero (listLength subarray)

divisibleSubarrays :
  List Int →
  Int →
  List (List Int)
divisibleSubarrays arr k =
  filterList
    (subarrayLengthDivisibleByNat (intToNat k))
    (allSubarrays arr)

subarraySums :
  List Int →
  Int →
  List Int
subarraySums arr k =
  mapList sumList (divisibleSubarrays arr k)

data _∈_ (x : Int) : List Int → Set where
  here : {xs : List Int} → x ∈ (x ∷ xs)
  there :
    {y : Int} →
    {xs : List Int} →
    x ∈ xs →
    x ∈ (y ∷ xs)

maxSubarraySumDivisibleByK-postcond :
  List Int →
  Int →
  Int →
  Set
maxSubarraySumDivisibleByK-postcond arr k result =
  let sums = subarraySums arr k
  in
    (listLength sums ≡ zero →
     result ≡ pos zero) ∧
    (zero < listLength sums →
     result ∈ sums ∧
     IsTrue
       (allList
         (λ sum → intLessOrEqual sum result)
         sums))

maxSubarraySumDivisibleByK-spec-satisfied : Set
maxSubarraySumDivisibleByK-spec-satisfied =
  (arr : List Int) →
  (k : Int) →
  maxSubarraySumDivisibleByK-postcond
    arr
    k
    (maxSubarraySumDivisibleByK arr k)
