-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/mergesort_list_OCamlMergesort_chopqtvc: the list-chopping verification
-- condition for recursive-call bounds and reconstruction from an abstract
-- prefix operation. This file contains no proof.

{-# OPTIONS --safe #-}

module mergesort_list_OCamlMergesort_chopqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≢_ _≤Z_ _<Z_
infixr 5 _++_
infixr 3 _∧_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

_≢_ : {A : Set} → A → A → Set
x ≢ y = Not (x ≡ y)

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

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

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = pos (length xs)

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

record PrefixModel (A : Set) : Set where
  field
    default : A
    prefix1 : Int → List A → List A
    prefix-def-zero :
      (xs : List A) →
      prefix1 zeroZ xs ≡ []
    prefix-def-cons-positive :
      (n : Int) →
      (x : A) →
      (xs : List A) →
      zeroZ <Z n →
      prefix1 n (x ∷ xs) ≡
        x ∷ prefix1 (subtractInt n oneZ) xs

open PrefixModel

NonzeroStepBounds : {A : Set} → Int → List A → Set
NonzeroStepBounds n [] = ⊥
NonzeroStepBounds n (_ ∷ tail) =
  let o1 = subtractInt n oneZ
  in
  ((zeroZ ≤Z n) ∧ (o1 <Z n))
  ∧ (zeroZ ≤Z o1)
  ∧ (o1 ≤Z lengthZ tail)

NonzeroObligation : {A : Set} → Int → List A → Set
NonzeroObligation n xs =
  n ≢ zeroZ →
  NonzeroStepBounds n xs

RecursiveResultPremise :
  {A : Set} →
  PrefixModel A →
  Int →
  List A →
  List A →
  Set
RecursiveResultPremise model n [] result = ⊥
RecursiveResultPremise model n (_ ∷ tail) result =
  tail ≡
    prefix1 model (subtractInt n oneZ) tail ++ result

ResultPremise :
  {A : Set} →
  PrefixModel A →
  Int →
  List A →
  List A →
  Set
ResultPremise model n xs result =
  IfSet
    (intEqual n zeroZ)
    (result ≡ xs)
    (RecursiveResultPremise model n xs result)

Reconstruction :
  {A : Set} →
  PrefixModel A →
  Int →
  List A →
  Set
Reconstruction {A} model n xs =
  (result : List A) →
  ResultPremise model n xs result →
  xs ≡ prefix1 model n xs ++ result

ChopVC :
  {A : Set} →
  PrefixModel A →
  Int →
  List A →
  Set
ChopVC model n xs =
  NonzeroObligation n xs
  ∧ Reconstruction model n xs

chop'vc : Set₁
chop'vc =
  (A : Set) →
  (model : PrefixModel A) →
  (n : Int) →
  (xs : List A) →
  zeroZ ≤Z n →
  n ≤Z lengthZ xs →
  ChopVC model n xs
