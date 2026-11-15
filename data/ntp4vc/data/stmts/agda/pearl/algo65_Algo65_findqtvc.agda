-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/algo65_Algo65_findqtvc: a selection-algorithm verification condition
-- expressing preservation of a list segment's permutation and the ordering
-- around a chosen pivot through partitioning and recursive calls.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module algo65_Algo65_findqtvc where

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

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

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

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

addInt : Int → Int → Int
addInt (pos m) (pos n) = pos (m + n)
addInt (pos m) (negsuc n) = difference m (suc n)
addInt (negsuc m) (pos n) = difference n (suc m)
addInt (negsuc m) (negsuc n) = negsuc (suc (m + n))

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

natToInt : Nat → Int
natToInt = pos

zeroZ oneZ fortyTwoZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
fortyTwoZ = pos 42

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

natSubtract : Nat → Nat → Nat
natSubtract n zero = n
natSubtract zero (suc _) = zero
natSubtract (suc m) (suc n) = natSubtract m n

take : {A : Set} → Nat → List A → List A
take zero _ = []
take (suc _) [] = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : {A : Set} → Nat → List A → List A
drop zero xs = xs
drop (suc _) [] = []
drop (suc n) (_ ∷ xs) = drop n xs

slice : {A : Set} → List A → Nat → Nat → List A
slice xs lower upper =
  take (natSubtract upper lower) (drop lower xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) = nthDefault default n xs

nthInt : List Int → Int → Int
nthInt xs index = nthDefault zeroZ (toNat index) xs

data Perm {A : Set} : List A → List A → Set where
  permNil :
    Perm [] []

  permKeep :
    {x : A} {xs ys : List A} →
    Perm xs ys →
    Perm (x ∷ xs) (x ∷ ys)

  permSwap :
    (x y : A) →
    (xs : List A) →
    Perm (x ∷ y ∷ xs) (y ∷ x ∷ xs)

  permTrans :
    {xs ys zs : List A} →
    Perm xs ys →
    Perm ys zs →
    Perm xs zs

permutSub' : {A : Set} → List A → List A → Nat → Nat → Set
permutSub' xs ys lower upper =
  (length xs ≡ length ys) ∧
  (slice xs zero lower ≡ slice ys zero lower) ∧
  (slice xs upper (length xs) ≡ slice ys upper (length xs)) ∧
  Perm (slice xs lower upper) (slice ys lower upper)

partitionState :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Int →
  Set
partitionState original current m n j i =
  ((m ≤Z j) ∧ (j <Z i) ∧ (i ≤Z n)) ∧
  permutSub'
    original
    current
    (toNat m)
    (toNat (addInt n oneZ)) ∧
  ((r : Int) →
    ((m ≤Z r) ∧ (r ≤Z j)) →
    nthInt current r ≤Z fortyTwoZ) ∧
  ((r : Int) →
    ((j <Z r) ∧ (r <Z i)) →
    nthInt current r ≡ fortyTwoZ) ∧
  ((r : Int) →
    ((i ≤Z r) ∧ (r ≤Z n)) →
    fortyTwoZ ≤Z nthInt current r)

pivotOrdering : List Int → Int → Int → Int → Set
pivotOrdering values lower pivot upper =
  ((r : Int) →
    ((lower ≤Z r) ∧ (r ≤Z pivot)) →
    nthInt values r ≤Z nthInt values pivot) ∧
  ((r : Int) →
    ((pivot ≤Z r) ∧ (r ≤Z upper)) →
    nthInt values pivot ≤Z nthInt values r)

selectionResult :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Set
selectionResult original result m k n =
  permutSub'
    original
    result
    (toNat m)
    (toNat (addInt n oneZ)) ∧
  pivotOrdering result m k n

FindVC : Int → Int → Int → List Int → Set
FindVC m k n a =
  (zeroZ ≤Z m) →
  (m ≤Z k) →
  (k ≤Z n) →
  (n <Z natToInt (length a)) →
  IfSet
    (intLess m n)
    (((zeroZ ≤Z m) ∧
      (m <Z n) ∧
      (n <Z natToInt (length a))) ∧
     ((j i : Int) →
      (a₁ : List Int) →
      (length a₁ ≡ length a) →
      partitionState a a₁ m n j i →
      IfSet
        (intLessOrEqual k j)
        (((zeroZ ≤Z subtractInt n m) ∧
          (subtractInt j m <Z subtractInt n m)) ∧
         (zeroZ ≤Z m) ∧
         (m ≤Z k) ∧
         (k ≤Z j) ∧
         (j <Z natToInt (length a₁)) ∧
         ((a₂ : List Int) →
          (length a₂ ≡ length a₁) →
          (permutSub'
            a₁
            a₂
            (toNat m)
            (toNat (addInt j oneZ)) ∧
           pivotOrdering a₂ m k j) →
          IfSet
            (intLessOrEqual i k)
            (((zeroZ ≤Z subtractInt n m) ∧
              (subtractInt n i <Z subtractInt n m)) ∧
             (zeroZ ≤Z i) ∧
             (i ≤Z k) ∧
             (k ≤Z n) ∧
             (n <Z natToInt (length a₂)) ∧
             ((a₃ : List Int) →
              (length a₃ ≡ length a₂) →
              (permutSub'
                a₂
                a₃
                (toNat i)
                (toNat (addInt n oneZ)) ∧
               pivotOrdering a₃ i k n) →
              selectionResult a a₃ m k n))
            (selectionResult a a₂ m k n)))
        (IfSet
          (intLessOrEqual i k)
          (((zeroZ ≤Z subtractInt n m) ∧
            (subtractInt n i <Z subtractInt n m)) ∧
           (zeroZ ≤Z i) ∧
           (i ≤Z k) ∧
           (k ≤Z n) ∧
           (n <Z natToInt (length a₁)) ∧
           ((a₂ : List Int) →
            (length a₂ ≡ length a₁) →
            (permutSub'
              a₁
              a₂
              (toNat i)
              (toNat (addInt n oneZ)) ∧
             pivotOrdering a₂ i k n) →
            selectionResult a a₂ m k n))
          (selectionResult a a₁ m k n))))
    (selectionResult a a m k n)

find'vc : Set
find'vc =
  (m k n : Int) →
  (a : List Int) →
  FindVC m k n a
