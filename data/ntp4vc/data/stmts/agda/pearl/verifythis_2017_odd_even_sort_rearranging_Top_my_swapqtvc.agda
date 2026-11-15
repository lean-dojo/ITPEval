-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2017_odd_even_sort_rearranging_Top_my_swapqtvc: swapping
-- an earlier larger integer-array entry with a later smaller entry preserves
-- the exchange relation and strictly decreases the entropy sum. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2017OddEvenSortRearrangingTopMySwapQtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

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

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negateInt (pos (m * suc n))
multiplyInt (negsuc m) (pos n) =
  negateInt (pos (suc m * n))
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

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
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

nthInt : List Int → Int → Int
nthInt xs index = nthDefault zeroZ (toNat index) xs

setAt : {A : Set} → List A → Nat → A → List A
setAt [] _ value = []
setAt (_ ∷ xs) zero value = value ∷ xs
setAt (x ∷ xs) (suc n) value =
  x ∷ setAt xs n value

arrayExchange : List Int → List Int → Int → Int → Set
arrayExchange old new firstIndex secondIndex =
  new ≡
    setAt
      (setAt old
        (toNat firstIndex)
        (nthInt old secondIndex))
      (toNat secondIndex)
      (nthInt old firstIndex)

aux : (Int → Int) → Int → Int → Int
aux values m index =
  multiplyInt index (subtractInt m (values index))

entropyFrom : List Int → Int → Int → Int
entropyFrom [] m index = zeroZ
entropyFrom (x ∷ xs) m index =
  addInt
    (multiplyInt index (subtractInt m x))
    (entropyFrom xs m (addInt index oneZ))

entropy : List Int → Int → Int
entropy values m = entropyFrom values m zeroZ

my-swap'vc : Set
my-swap'vc =
  (a : List Int) →
  (j i m : Int) →
  nthInt a j <Z nthInt a i →
  zeroZ ≤Z i →
  i <Z j →
  j <Z lengthZ a →
  zeroZ ≤Z i ∧
  i <Z lengthZ a ∧
  zeroZ ≤Z j ∧
  j <Z lengthZ a ∧
  ((a1 : List Int) →
   length a1 ≡ length a →
   arrayExchange a a1 i j →
   arrayExchange a a1 i j ∧
   entropy a1 m <Z entropy a m)
