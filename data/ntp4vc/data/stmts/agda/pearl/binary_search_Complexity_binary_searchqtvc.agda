-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/binary_search_Complexity_binary_searchqtvc: a binary-search
-- verification condition preserving sortedness-based exclusion invariants
-- and a logarithmic running-time bound. This file contains no proof.

{-# OPTIONS --safe #-}

module binary_search_Complexity_binary_searchqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_
infixr 2 _∨_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

IfInt : Bool → Int → Int → Int
IfInt true when-true when-false = when-true
IfInt false when-true when-false = when-false

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natHalf : Nat → Nat
natHalf zero = zero
natHalf (suc zero) = zero
natHalf (suc (suc n)) = suc (natHalf n)

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

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

quotientByTwo : Int → Int
quotientByTwo (pos n) = pos (natHalf n)
quotientByTwo (negsuc n) = negative (natHalf (suc n))

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

natToInt : Nat → Int
natToInt = pos

zeroZ oneZ twoZ minusOneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))
minusOneZ = negsuc zero

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = natToInt (length xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) = nthDefault default n xs

nthInt : List Int → Int → Int
nthInt xs index = nthDefault zeroZ (toNat index) xs

record Log2Structure : Set where
  field
    log2 : Int → Int
    log2-def :
      (n : Int) →
      IfSet
        (intLessOrEqual n oneZ)
        (log2 n ≡ zeroZ)
        (log2 n ≡ addInt oneZ (log2 (quotientByTwo n)))

open Log2Structure

complexity : Log2Structure → Int → Int
complexity sig n =
  IfInt
    (intEqual n zeroZ)
    zeroZ
    (addInt oneZ (log2 sig n))

Sorted : List Int → Set
Sorted xs =
  (i₁ i₂ : Int) →
  ((zeroZ ≤Z i₁) ∧ (i₁ ≤Z i₂) ∧ (i₂ <Z lengthZ xs)) →
  nthInt xs i₁ ≤Z nthInt xs i₂

OutsideAbsent :
  List Int →
  Int →
  Int →
  Int →
  Set
OutsideAbsent xs value lower upper =
  (i : Int) →
  (((zeroZ ≤Z i) ∧ (i <Z lower)) ∨
   ((upper ≤Z i) ∧ (i <Z lengthZ xs))) →
  Not (nthInt xs i ≡ value)

AllAbsent : List Int → Int → Set
AllAbsent xs value =
  (i : Int) →
  ((zeroZ ≤Z i) ∧ (i <Z lengthZ xs)) →
  Not (nthInt xs i ≡ value)

LoopInvariant :
  Log2Structure →
  List Int →
  Int →
  Int →
  Int →
  Int →
  Set
LoopInvariant sig xs value time lower upper =
  ((zeroZ ≤Z lower) ∧
   (lower ≤Z upper) ∧
   (upper ≤Z lengthZ xs)) ∧
  OutsideAbsent xs value lower upper ∧
  addInt
    (subtractInt time zeroZ)
    (complexity sig (subtractInt upper lower))
    ≤Z complexity sig (lengthZ xs)

SearchStep :
  Log2Structure →
  List Int →
  Int →
  Int →
  Int →
  Int →
  Set
SearchStep sig xs value high low time =
  IfSet
    (intLess low high)
    (Not (twoZ ≡ zeroZ) ∧
     (let middle =
            addInt low
              (quotientByTwo (subtractInt high low))
      in
      ((zeroZ ≤Z middle) ∧ (middle <Z lengthZ xs)) ∧
      IfSet
        (intLess (nthInt xs middle) value)
        (((zeroZ ≤Z subtractInt high low) ∧
          (subtractInt high (addInt middle oneZ)
            <Z subtractInt high low)) ∧
         LoopInvariant
           sig
           xs
           value
           (addInt time oneZ)
           (addInt middle oneZ)
           high)
        (((zeroZ ≤Z middle) ∧ (middle <Z lengthZ xs)) ∧
         IfSet
           (intLess value (nthInt xs middle))
           (((zeroZ ≤Z subtractInt high low) ∧
             (subtractInt middle low
               <Z subtractInt high low)) ∧
            LoopInvariant
              sig
              xs
              value
              (addInt time oneZ)
              low
              middle)
           (((((zeroZ ≤Z middle) ∧
               (middle <Z lengthZ xs)) ∧
              (nthInt xs middle ≡ value)) ∨
             ((middle ≡ minusOneZ) ∧
              AllAbsent xs value)) ∧
            (subtractInt time zeroZ
              ≤Z complexity sig (lengthZ xs))))))
    (((((zeroZ ≤Z minusOneZ) ∧
        (minusOneZ <Z lengthZ xs)) ∧
       (nthInt xs minusOneZ ≡ value)) ∨
      AllAbsent xs value) ∧
     (subtractInt time zeroZ
       ≤Z complexity sig (lengthZ xs)))

BinarySearchVC :
  Log2Structure →
  List Int →
  Int →
  Set
BinarySearchVC sig xs value =
  Sorted xs →
  LoopInvariant
    sig
    xs
    value
    zeroZ
    zeroZ
    (lengthZ xs) ∧
  ((high low time : Int) →
   LoopInvariant sig xs value time low high →
   SearchStep sig xs value high low time)

binary-search'vc : (sig : Log2Structure) → Set
binary-search'vc sig =
  (xs : List Int) →
  (value : Int) →
  BinarySearchVC sig xs value
