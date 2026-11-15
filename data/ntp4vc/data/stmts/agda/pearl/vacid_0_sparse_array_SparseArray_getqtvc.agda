-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/vacid_0_sparse_array_SparseArray_getqtvc: the sparse-array get
-- verification condition, relating an in-bounds lookup branch to the
-- abstract sparse-array value. This file contains no proof.

{-# OPTIONS --safe #-}

module Vacid0SparseArraySparseArrayGetQtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record Inhabited (A : Set) : Set where
  constructor inhabited
  field
    default : A

open Inhabited

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

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

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
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

_≤Z_ : Int → Int → Set
x ≤Z y = intLessOrEqual x y ≡ true

_<Z_ : Int → Int → Set
x <Z y = intLess x y ≡ true

andBool : Bool → Bool → Bool
andBool true right = right
andBool false right = false

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

IfValue : {A : Set} → Bool → A → A → A
IfValue true when-true when-false = when-true
IfValue false when-true when-false = when-false

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

lengthList : {A : Set} → List A → Nat
lengthList [] = zero
lengthList (_ ∷ xs) = suc (lengthList xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = pos (lengthList xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault fallback zero [] = fallback
nthDefault fallback zero (x ∷ xs) = x
nthDefault fallback (suc n) [] = fallback
nthDefault fallback (suc n) (_ ∷ xs) =
  nthDefault fallback n xs

zeroZ maxLengthZ : Int
zeroZ = pos zero
maxLengthZ = pos 1000

nthInt : List Int → Int → Int
nthInt xs i = nthDefault zeroZ (toNat i) xs

record SparseArray (A : Set) : Set where
  constructor sparse-array
  field
    values : List A
    index  : List Int
    back   : List Int
    card   : Int
    def    : A
    invariant :
      zeroZ ≤Z card ∧
      card ≤Z lengthZ values ∧
      lengthZ values ≤Z maxLengthZ ∧
      lengthList values ≡ lengthList index ∧
      lengthList index ≡ lengthList back ∧
      ((i : Int) →
        (zeroZ ≤Z i ∧ i <Z card) →
        (zeroZ ≤Z nthInt back i ∧
         nthInt back i <Z lengthZ values) ∧
        nthInt index (nthInt back i) ≡ i)

open SparseArray public

isEltBool : {A : Set} → SparseArray A → Int → Bool
isEltBool a i =
  andBool
    (intLessOrEqual zeroZ (nthInt (index a) i))
    (andBool
      (intLess (nthInt (index a) i) (card a))
      (intEqual
        (nthInt (back a) (nthInt (index a) i))
        i))

isElt : {A : Set} → SparseArray A → Int → Set
isElt a i = isEltBool a i ≡ true

nthValue :
  {A : Set} →
  Inhabited A →
  SparseArray A →
  Int →
  A
nthValue inhabitant a i =
  nthDefault
    (default inhabitant)
    (toNat i)
    (values a)

value :
  {A : Set} →
  Inhabited A →
  SparseArray A →
  Int →
  A
value inhabitant a i =
  IfValue
    (isEltBool a i)
    (nthValue inhabitant a i)
    (def a)

sparseLength : {A : Set} → SparseArray A → Int
sparseLength a = lengthZ (values a)

resultPremise :
  {A : Set} →
  Inhabited A →
  SparseArray A →
  Int →
  A →
  Set
resultPremise inhabitant a i result =
  IfSet
    (isEltBool a i)
    (result ≡ nthValue inhabitant a i)
    (result ≡ def a)

get'vc : Set₁
get'vc =
  (A : Set) →
  (inhabitant : Inhabited A) →
  (i : Int) →
  (a : SparseArray A) →
  zeroZ ≤Z i →
  i <Z sparseLength a →
  zeroZ ≤Z i ∧
  i <Z sparseLength a ∧
  (isElt a i →
    zeroZ ≤Z i ∧ i <Z lengthZ (values a)) ∧
  ((result : A) →
    resultPremise inhabitant a i result →
    result ≡ value inhabitant a i)
