-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/mergesort_list_OCamlMergesort_mergesortqtvc: the list mergesort
-- verification condition asserting sortedness and permutation preservation
-- for both the short-list and recursive branches. This file contains no proof.

{-# OPTIONS --safe #-}

module mergesort_list_OCamlMergesort_mergesortqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_ _∈_
infixr 5 _++_
infixr 3 _∧_
infixr 2 _∨_
infix 1 _↔_

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

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

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

zeroZ oneZ twoZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = pos (length xs)

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data _∈_ {A : Set} (x : A) : List A → Set where
  here :
    {xs : List A} →
    x ∈ (x ∷ xs)

  there :
    {y : A} {xs : List A} →
    x ∈ xs →
    x ∈ (y ∷ xs)

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

data Sorted {A : Set} (le : A → A → Set) : List A → Set where
  sortedNil :
    Sorted le []

  sortedOne :
    (x : A) →
    Sorted le (x ∷ [])

  sortedTwo :
    (x y : A) →
    (xs : List A) →
    le x y →
    Sorted le (y ∷ xs) →
    Sorted le (x ∷ y ∷ xs)

record MergesortModel (Elt : Set) : Set₁ where
  field
    eltDefault : Elt

    le : Elt → Elt → Set
    leRefl :
      (x : Elt) →
      le x x
    leTrans :
      (x y z : Elt) →
      le x y →
      le y z →
      le x z
    leTotal :
      (x y : Elt) →
      le x y ∨ le y x

    sortedMem :
      (xs : List Elt) →
      (x : Elt) →
      (((y : Elt) → y ∈ xs → le x y) ∧ Sorted le xs)
        ↔ Sorted le (x ∷ xs)

    sortedAppend :
      (xs ys : List Elt) →
      (Sorted le xs ∧
       Sorted le ys ∧
       ((x y : Elt) → x ∈ xs → y ∈ ys → le x y))
        ↔ Sorted le (xs ++ ys)

    prefix1 :
      {A : Set} →
      A →
      Int →
      List A →
      List A

    prefixDefZero :
      {A : Set} →
      (default : A) →
      (xs : List A) →
      prefix1 default zeroZ xs ≡ []

    prefixDefConsPositive :
      {A : Set} →
      (default : A) →
      (n : Int) →
      (x : A) →
      (xs : List A) →
      zeroZ <Z n →
      prefix1 default n (x ∷ xs) ≡
        x ∷ prefix1 default (subtractInt n oneZ) xs

open MergesortModel

ResultPremise :
  {Elt : Set} →
  MergesortModel Elt →
  List Elt →
  List Elt →
  Set
ResultPremise model xs result =
  let n = lengthZ xs
  in
  IfSet
    (intLess n twoZ)
    (result ≡ xs)
    (Sorted (le model) result ∧
     Perm result (prefix1 model (eltDefault model) n xs))

ResultConclusion :
  {Elt : Set} →
  MergesortModel Elt →
  List Elt →
  Set
ResultConclusion {Elt} model xs =
  (result : List Elt) →
  ResultPremise model xs result →
  Sorted (le model) result ∧ Perm result xs

MergesortVC :
  {Elt : Set} →
  MergesortModel Elt →
  List Elt →
  Set
MergesortVC model xs =
  let n = lengthZ xs
  in
  (Not (n <Z twoZ) →
    (twoZ ≤Z n ∧ n ≤Z lengthZ xs))
  ∧ ResultConclusion model xs

mergesort'vc : Set₁
mergesort'vc =
  (Elt : Set) →
  (model : MergesortModel Elt) →
  (xs : List Elt) →
  MergesortVC model xs
