-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/flag2_Flag_swapqtvc: the list-swap verification condition preserving
-- exchanged colors, all other entries, and color occurrence counts on every
-- interval containing both swapped indices. This file contains no proof.

{-# OPTIONS --safe #-}

module flag2_Flag_swapqtvc where

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

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

natToInt : Nat → Int
natToInt = pos

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = natToInt (length xs)

data Color : Set where
  Blue  : Color
  White : Color
  Red   : Color

IfColor : Bool → Color → Color → Color
IfColor true when-true when-false = when-true
IfColor false when-true when-false = when-false

colorEqual : Color → Color → Bool
colorEqual Blue Blue = true
colorEqual Blue White = false
colorEqual Blue Red = false
colorEqual White Blue = false
colorEqual White White = true
colorEqual White Red = false
colorEqual Red Blue = false
colorEqual Red White = false
colorEqual Red Red = true

record Signature : Set where
  field
    defaultColor : Color
    nbOcc        : (Int → Color) → Int → Int → Color → Int

open Signature

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) = nthDefault default n xs

nthColor : Signature → List Color → Int → Color
nthColor sig xs index =
  nthDefault (defaultColor sig) (toNat index) xs

setAt : {A : Set} → List A → Nat → A → List A
setAt [] _ value = []
setAt (_ ∷ xs) zero value = value ∷ xs
setAt (x ∷ xs) (suc n) value = x ∷ setAt xs n value

updateColor : (Int → Color) → Int → Color → Int → Color
updateColor values index value query =
  IfColor (intEqual query index) value (values query)

record Laws (sig : Signature) : Set where
  field
    nbOccDef :
      (j i : Int) →
      (values : Int → Color) →
      (color : Color) →
      IfSet
        (intLessOrEqual j i)
        (nbOcc sig values i j color ≡ zeroZ)
        (IfSet
          (colorEqual (values (subtractInt j oneZ)) color)
          (nbOcc sig values i j color ≡
           addInt oneZ
             (nbOcc sig values i (subtractInt j oneZ) color))
          (nbOcc sig values i j color ≡
           nbOcc sig values i (subtractInt j oneZ) color))

Monochrome : (Int → Color) → Int → Int → Color → Set
Monochrome values lower upper color =
  (k : Int) →
  ((lower ≤Z k) ∧ (k <Z upper)) →
  values k ≡ color

UnchangedExcept :
  Signature →
  List Color →
  List Color →
  Int →
  Int →
  Set
UnchangedExcept sig before after firstIndex secondIndex =
  (k : Int) →
  (Not (k ≡ firstIndex) ∧ Not (k ≡ secondIndex)) →
  nthColor sig after k ≡ nthColor sig before k

CountsOnContainingIntervalPreserved :
  Signature →
  List Color →
  List Color →
  Int →
  Int →
  Set
CountsOnContainingIntervalPreserved
  sig before after firstIndex secondIndex =
  (lower upper : Int) →
  (color : Color) →
  (((lower ≤Z firstIndex) ∧ (firstIndex <Z upper)) ∧
   (lower ≤Z secondIndex) ∧ (secondIndex <Z upper)) →
  nbOcc sig (nthColor sig after) lower upper color ≡
  nbOcc sig (nthColor sig before) lower upper color

SwapConsequences :
  Signature →
  List Color →
  List Color →
  Int →
  Int →
  Set
SwapConsequences sig original swapped i j =
  nthColor sig swapped i ≡ nthColor sig original j ∧
  nthColor sig swapped j ≡ nthColor sig original i ∧
  UnchangedExcept sig original swapped i j ∧
  CountsOnContainingIntervalPreserved sig original swapped i j

SwapConclusion :
  Signature →
  Int →
  List Color →
  Int →
  Set
SwapConclusion sig i original j =
  (zeroZ ≤Z i) ∧
  (i <Z lengthZ original) ∧
  (let ai = nthColor sig original i
   in
   ((zeroZ ≤Z j) ∧ (j <Z lengthZ original)) ∧
   (let aj = nthColor sig original j
        firstUpdate = setAt original (toNat i) aj
        swapped = setAt firstUpdate (toNat j) ai
    in
    ((zeroZ ≤Z i) ∧ (i <Z lengthZ original)) ∧
    ((length firstUpdate ≡ length original) →
     ((query : Int) →
      nthColor sig firstUpdate query ≡
      updateColor (nthColor sig original) i aj query) →
     ((zeroZ ≤Z j) ∧ (j <Z lengthZ firstUpdate)) ∧
     ((length swapped ≡ length firstUpdate) →
      ((query : Int) →
       nthColor sig swapped query ≡
       updateColor (nthColor sig firstUpdate) j ai query) →
      SwapConsequences sig original swapped i j))))

swap'vc : Set
swap'vc =
  (sig : Signature) →
  Laws sig →
  (i : Int) →
  (original : List Color) →
  (j : Int) →
  (zeroZ ≤Z i) →
  (i <Z lengthZ original) →
  (zeroZ ≤Z j) →
  (j <Z lengthZ original) →
  SwapConclusion sig i original j
