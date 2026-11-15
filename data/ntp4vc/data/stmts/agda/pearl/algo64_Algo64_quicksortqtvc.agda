-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/algo64_Algo64_quicksortqtvc: a quicksort verification condition
-- expressing preservation of a list segment's permutation and sortedness
-- after partitioning and recursive sorting. This file contains no proof.

{-# OPTIONS --safe #-}

module algo64_Algo64_quicksortqtvc where

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

sortedSub : (Int → Int) → Int → Int → Set
sortedSub values lower upper =
  (i₁ i₂ : Int) →
  ((lower ≤Z i₁) ∧ (i₁ ≤Z i₂) ∧ (i₂ <Z upper)) →
  values i₁ ≤Z values i₂

sortedSub1 : List Int → Int → Int → Set
sortedSub1 xs lower upper =
  sortedSub (nthInt xs) lower upper

qs-partition :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Set
qs-partition t₁ t₂ m n i j x =
  permutSub' t₁ t₂ (toNat m) (toNat (addInt n oneZ)) ∧
  ((k : Int) →
    ((m ≤Z k) ∧ (k ≤Z j)) →
    nthInt t₂ k ≤Z x) ∧
  ((k : Int) →
    ((j <Z k) ∧ (k <Z i)) →
    nthInt t₂ k ≡ x) ∧
  ((k : Int) →
    ((i ≤Z k) ∧ (k ≤Z n)) →
    x ≤Z nthInt t₂ k)

QuicksortVC : Int → Int → List Int → Set
QuicksortVC m n a =
  (zeroZ ≤Z m) →
  (m ≤Z n) →
  (n <Z natToInt (length a)) →
  IfSet
    (intLess m n)
    (((zeroZ ≤Z m) ∧ (m <Z n) ∧
      (n <Z natToInt (length a))) ∧
     ((j i : Int) →
      (a₁ : List Int) →
      (length a₁ ≡ length a) →
      (((m ≤Z j) ∧ (j <Z i) ∧ (i ≤Z n)) ∧
       permutSub' a a₁ (toNat m) (toNat (addInt n oneZ)) ∧
       ((r : Int) →
        ((m ≤Z r) ∧ (r ≤Z j)) →
        nthInt a₁ r ≤Z fortyTwoZ) ∧
       ((r : Int) →
        ((j <Z r) ∧ (r <Z i)) →
        nthInt a₁ r ≡ fortyTwoZ) ∧
       ((r : Int) →
        ((i ≤Z r) ∧ (r ≤Z n)) →
        fortyTwoZ ≤Z nthInt a₁ r)) →
      ((((zeroZ ≤Z subtractInt n m) ∧
         (subtractInt j m <Z subtractInt n m)) ∧
        (zeroZ ≤Z m) ∧
        (m ≤Z j) ∧
        (j <Z natToInt (length a₁))) ∧
       ((a₂ : List Int) →
        (length a₂ ≡ length a₁) →
        (permutSub' a₁ a₂
          (toNat m)
          (toNat (addInt j oneZ)) ∧
         sortedSub1 a₂ m (addInt j oneZ)) →
        ((((zeroZ ≤Z subtractInt n m) ∧
           (subtractInt n i <Z subtractInt n m)) ∧
          (zeroZ ≤Z i) ∧
          (i ≤Z n) ∧
          (n <Z natToInt (length a₂))) ∧
         ((a₃ : List Int) →
          (length a₃ ≡ length a₂) →
          (permutSub' a₂ a₃
            (toNat i)
            (toNat (addInt n oneZ)) ∧
           sortedSub1 a₃ i (addInt n oneZ)) →
          (permutSub' a a₃
            (toNat m)
            (toNat (addInt n oneZ)) ∧
           sortedSub1 a₃ m (addInt n oneZ))))))))
    (permutSub' a a
      (toNat m)
      (toNat (addInt n oneZ)) ∧
     sortedSub1 a m (addInt n oneZ))

quicksort'vc : Set
quicksort'vc =
  (m n : Int) →
  (a : List Int) →
  QuicksortVC m n a
