-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/quicksort_Shuffle_shuffleqtvc: the verification condition for
-- Knuth's shuffle of an integer array, requiring every bounded swap to
-- preserve permutation of the original array. This file contains no proof.

{-# OPTIONS --safe #-}

module quicksort_Shuffle_shuffleqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

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

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

negateInt : Int → Int
negateInt (pos n) = negative n
negateInt (negsuc n) = pos (suc n)

differenceNat : Nat → Nat → Int
differenceNat zero zero = pos zero
differenceNat (suc m) zero = pos (suc m)
differenceNat zero (suc n) = negsuc n
differenceNat (suc m) (suc n) = differenceNat m n

addInt : Int → Int → Int
addInt (pos m) (pos n) = pos (m + n)
addInt (pos m) (negsuc n) = differenceNat m (suc n)
addInt (negsuc m) (pos n) = differenceNat n (suc m)
addInt (negsuc m) (negsuc n) = negsuc (suc (m + n))

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = pos (length xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) = nthDefault default n xs

nthInt : List Int → Int → Int
nthInt xs index = nthDefault zeroZ (toNat index) xs

updateAt : {A : Set} → List A → Nat → A → List A
updateAt [] index value = []
updateAt (x ∷ xs) zero value = value ∷ xs
updateAt (x ∷ xs) (suc index) value =
  x ∷ updateAt xs index value

swapAt : List Int → Int → Int → List Int
swapAt xs i j =
  updateAt
    (updateAt xs (toNat i) (nthInt xs j))
    (toNat j)
    (nthInt xs i)

ArrayExchange : List Int → List Int → Int → Int → Set
ArrayExchange before after i j =
  after ≡ swapAt before i j

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

Bounds : Int → List Int → Set
Bounds index xs =
  zeroZ ≤Z index ∧ index <Z lengthZ xs

ShuffleVC : List Int → Set
ShuffleVC original =
  let last-index = subtractInt (lengthZ original) oneZ
  in
  ((oneZ ≤Z addInt last-index oneZ) →
    Permutation original original ∧
    ((current : List Int) →
      length current ≡ length original →
      (index : Int) →
      ((oneZ ≤Z index ∧ index ≤Z last-index) ∧
        Permutation original current) →
      let random-bound = addInt index oneZ
      in
      zeroZ <Z random-bound ∧
      ((random-index : Int) →
        (zeroZ ≤Z random-index ∧
          random-index <Z random-bound) →
        (Bounds index current ∧ Bounds random-index current) ∧
        ((next : List Int) →
          length next ≡ length current →
          ArrayExchange current next index random-index →
          Permutation original next)))) ∧
  ((addInt last-index oneZ <Z oneZ) →
    Permutation original original)

shuffle'vc : Set
shuffle'vc =
  (original : List Int) →
  ShuffleVC original
