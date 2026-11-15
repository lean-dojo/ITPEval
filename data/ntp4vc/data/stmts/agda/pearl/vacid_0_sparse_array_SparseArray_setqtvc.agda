-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/vacid_0_sparse_array_SparseArray_setqtvc: the sparse-array set
-- verification condition, preserving the sparse-array invariant and the
-- updated-value specification through its insertion branch. This file contains no proof.

{-# OPTIONS --safe #-}

module Vacid0SparseArraySparseArraySetQtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

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

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

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

notBool : Bool → Bool
notBool true = false
notBool false = true

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

setAt : {A : Set} → List A → Nat → A → List A
setAt [] _ value = []
setAt (_ ∷ xs) zero value = value ∷ xs
setAt (x ∷ xs) (suc n) value = x ∷ setAt xs n value

FunctionEqual :
  {A B : Set} →
  (A → B) →
  (A → B) →
  Set
FunctionEqual f g = (x : _) → f x ≡ g x

updateInt :
  {A : Set} →
  (Int → A) →
  Int →
  A →
  Int →
  A
updateInt old target replacement query with intEqual query target
... | true = replacement
... | false = old query

zeroZ oneZ maxLengthZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
maxLengthZ = pos 1000

nthInt : List Int → Int → Int
nthInt xs i = nthDefault zeroZ (toNat i) xs

nthValue :
  {A : Set} →
  Inhabited A →
  List A →
  Int →
  A
nthValue inhabitant xs i =
  nthDefault (default inhabitant) (toNat i) xs

ArrayFunctionEqual :
  {A : Set} →
  List A →
  (Int → A) →
  (Int → A) →
  Set
ArrayFunctionEqual entries f g =
  (index : Int) →
  (zeroZ ≤Z index ∧ index <Z lengthZ entries) →
  f index ≡ g index

SparseInvariant :
  {A : Set} →
  List A →
  List Int →
  List Int →
  Int →
  Set
SparseInvariant values index back card =
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

record SparseArray (A : Set) : Set where
  constructor sparse-array
  field
    values    : List A
    index     : List Int
    back      : List Int
    card      : Int
    fallback  : A
    invariant : SparseInvariant values index back card

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

value :
  {A : Set} →
  Inhabited A →
  SparseArray A →
  Int →
  A
value inhabitant a i =
  IfValue
    (isEltBool a i)
    (nthValue inhabitant (values a) i)
    (fallback a)

sparseLength : {A : Set} → SparseArray A → Int
sparseLength a = lengthZ (values a)

UpdatePostcondition :
  {A : Set} →
  Inhabited A →
  SparseArray A →
  SparseArray A →
  Int →
  A →
  Set
UpdatePostcondition inhabitant original updated i v =
  value inhabitant updated i ≡ v ∧
  ((j : Int) →
    Not (j ≡ i) →
    value inhabitant updated j ≡ value inhabitant original j)

MatchesValueWrite :
  {A : Set} →
  SparseArray A →
  SparseArray A →
  Int →
  A →
  Set
MatchesValueWrite original updated i v =
  fallback original ≡ fallback updated ∧
  card original ≡ card updated ∧
  back original ≡ back updated ∧
  index original ≡ index updated ∧
  setAt (values original) (toNat i) v ≡ values updated

MatchesInsertion :
  {A : Set} →
  SparseArray A →
  SparseArray A →
  Int →
  Set
MatchesInsertion before after i =
  fallback before ≡ fallback after ∧
  addInt (card before) oneZ ≡ card after ∧
  setAt (back before) (toNat (card before)) i ≡ back after ∧
  setAt (index before) (toNat i) (card before) ≡ index after ∧
  values before ≡ values after

InsertionResult :
  {A : Set} →
  Inhabited A →
  SparseArray A →
  SparseArray A →
  Int →
  A →
  Set
InsertionResult {A} inhabitant original before i v =
  let updatedIndex =
        setAt (index before) (toNat i) (card before)
      updatedBack =
        setAt (back before) (toNat (card before)) i
  in
  (after : SparseArray A) →
  SparseInvariant
    (values before)
    updatedIndex
    updatedBack
    (addInt (card before) oneZ) ∧
  (MatchesInsertion before after i →
    UpdatePostcondition inhabitant original after i v)

BackWriteObligation :
  {A : Set} →
  Inhabited A →
  SparseArray A →
  SparseArray A →
  Int →
  A →
  Set
BackWriteObligation inhabitant original before i v =
  let updatedBack =
        setAt (back before) (toNat (card before)) i
  in
  lengthList updatedBack ≡ lengthList (back before) →
  lengthList updatedBack ≡ lengthList (back before) →
  ArrayFunctionEqual updatedBack
    (nthInt updatedBack)
    (updateInt (nthInt (back before)) (card before) i) →
  InsertionResult inhabitant original before i v

IndexWriteObligation :
  {A : Set} →
  Inhabited A →
  SparseArray A →
  SparseArray A →
  Int →
  A →
  Set
IndexWriteObligation inhabitant original before i v =
  let oldIndex = index before
      updatedIndex = setAt oldIndex (toNat i) (card before)
  in
  lengthList updatedIndex ≡ lengthList oldIndex →
  lengthList updatedIndex ≡ lengthList (index before) →
  ArrayFunctionEqual updatedIndex
    (nthInt updatedIndex)
    (updateInt (nthInt oldIndex) i (card before)) →
  (zeroZ ≤Z card before ∧
   card before <Z lengthZ (back before)) ∧
  BackWriteObligation inhabitant original before i v

InsertionBranch :
  {A : Set} →
  Inhabited A →
  SparseArray A →
  SparseArray A →
  Int →
  A →
  Set
InsertionBranch inhabitant original before i v =
  zeroZ ≤Z i ∧
  i <Z lengthZ (index before) ∧
  IndexWriteObligation inhabitant original before i v

AfterValueWrite :
  {A : Set} →
  Inhabited A →
  SparseArray A →
  SparseArray A →
  Int →
  A →
  Set
AfterValueWrite inhabitant original updated i v =
  (zeroZ ≤Z i ∧ i <Z sparseLength updated) ∧
  IfSet
    (notBool (isEltBool updated i))
    (InsertionBranch inhabitant original updated i v)
    (UpdatePostcondition inhabitant original updated i v)

ValueWriteObligation :
  {A : Set} →
  Inhabited A →
  SparseArray A →
  Int →
  A →
  Set
ValueWriteObligation {A} inhabitant a i v =
  let oldValues = values a
      updatedValues = setAt oldValues (toNat i) v
  in
  (a1 : SparseArray A) →
  lengthList updatedValues ≡ lengthList oldValues →
  lengthList updatedValues ≡ lengthList (values a) →
  ArrayFunctionEqual updatedValues
    (nthValue inhabitant updatedValues)
    (updateInt (nthValue inhabitant oldValues) i v) →
  SparseInvariant updatedValues (index a) (back a) (card a) ∧
  (MatchesValueWrite a a1 i v →
    AfterValueWrite inhabitant a a1 i v)

set'vc : Set₁
set'vc =
  (A : Set) →
  (inhabitant : Inhabited A) →
  (i : Int) →
  (a : SparseArray A) →
  (v : A) →
  zeroZ ≤Z i →
  i <Z sparseLength a →
  (zeroZ ≤Z i ∧ i <Z lengthZ (values a)) ∧
  ValueWriteObligation inhabitant a i v
