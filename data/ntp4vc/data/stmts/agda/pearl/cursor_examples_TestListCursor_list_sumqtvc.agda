-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/cursor_examples_TestListCursor_list_sumqtvc: a list-cursor summation
-- verification condition for prefix sums, single-element cursor advances,
-- termination decrease, and the completed list sum. This file contains no proof.

{-# OPTIONS --safe #-}

module cursor_examples_TestListCursor_list_sumqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

data Bottom : Set where

Not : Set → Set
Not proposition = proposition → Bottom

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

notBool : Bool → Bool
notBool true = false
notBool false = true

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

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

natToInt : Nat → Int
natToInt = pos

zeroZ : Int
zeroZ = pos zero

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = natToInt (length xs)

append : {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) = nthDefault default n xs

getClosure : List Int → Int → Int
getClosure xs index = nthDefault zeroZ (toNat index) xs

sumCount : (Int → Int) → Int → Nat → Int
sumCount f lower zero = zeroZ
sumCount f lower (suc n) =
  addInt
    (sumCount f lower n)
    (f (addInt lower (natToInt n)))

integerSum : (Int → Int) → Int → Int → Int
integerSum f lower upper =
  sumCount f lower (toNat (subtractInt upper lower))

listSum : List Int → Int
listSum [] = zeroZ
listSum (x ∷ xs) = addInt x (listSum xs)

record CursorModel : Set₁ where
  field
    Cursor     : Set
    visited    : Cursor → List Int
    collection : Cursor → List Int

open CursorModel

permitted : (model : CursorModel) → Cursor model → Set
permitted model cursor =
  (natLessOrEqual
    (length (visited model cursor))
    (length (collection model cursor)) ≡ true) ∧
  ((index : Int) →
    ((zeroZ ≤Z index) ∧
     (index <Z lengthZ (visited model cursor))) →
    getClosure (visited model cursor) index ≡
      getClosure (collection model cursor) index)

complete : (model : CursorModel) → Cursor model → Set
complete model cursor =
  length (visited model cursor) ≡
    length (collection model cursor)

ExtensionConclusion :
  (model : CursorModel) →
  List Int →
  Cursor model →
  Cursor model →
  Int →
  Set
ExtensionConclusion model whole before after x =
  ((zeroZ ≤Z
      subtractInt
        (lengthZ whole)
        (lengthZ (visited model before))) ∧
   (subtractInt
      (lengthZ whole)
      (lengthZ (visited model after)) <Z
    subtractInt
      (lengthZ whole)
      (lengthZ (visited model before)))) ∧
  (addInt
      (integerSum
        (getClosure (visited model before))
        zeroZ
        (lengthZ (visited model before)))
      x ≡
   integerSum
      (getClosure (visited model after))
      zeroZ
      (lengthZ (visited model after))) ∧
  permitted model after

ExtensionStep :
  (model : CursorModel) →
  List Int →
  Cursor model →
  Cursor model →
  Set
ExtensionStep model whole before after =
  collection model after ≡ collection model before →
  (x : Int) →
  (visited model after ≡
    append (visited model before) (x ∷ [])) ∧
  permitted model after →
  ExtensionConclusion model whole before after x

CursorCase :
  (model : CursorModel) →
  List Int →
  Cursor model →
  Set
CursorCase model whole cursor =
  permitted model cursor ∧
  IfSet
    (notBool
      (natEqual
        (length (visited model cursor))
        (length (collection model cursor))))
    ((Not (complete model cursor) ∧ permitted model cursor) ∧
     ((next : Cursor model) →
       ExtensionStep model whole cursor next))
    (integerSum
      (getClosure (visited model cursor))
      zeroZ
      (lengthZ (visited model cursor)) ≡
     listSum whole)

ListSumVC :
  (model : CursorModel) →
  Cursor model →
  List Int →
  Set
ListSumVC model cursor whole =
  permitted model cursor →
  visited model cursor ≡ [] →
  collection model cursor ≡ whole →
  (zeroZ ≡
    integerSum
      (getClosure (visited model cursor))
      zeroZ
      (lengthZ (visited model cursor))) ∧
  permitted model cursor ∧
  ((next : Cursor model) →
    collection model next ≡ collection model cursor →
    permitted model next →
    CursorCase model whole next)

list-sum'vc : Set₁
list-sum'vc =
  (model : CursorModel) →
  (cursor : Cursor model) →
  (whole : List Int) →
  ListSumVC model cursor whole
