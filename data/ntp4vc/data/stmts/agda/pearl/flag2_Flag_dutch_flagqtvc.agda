-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/flag2_Flag_dutch_flagqtvc: the Dutch-national-flag loop verification
-- condition preserving blue, white, and red segments and color occurrence
-- counts through swaps. This file contains no proof.

{-# OPTIONS --safe #-}

module flag2_Flag_dutch_flagqtvc where

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

record Exists₂ (A B : Set) (P : A → B → Set) : Set where
  constructor witnesses
  field
    firstWitness  : A
    secondWitness : B
    property      : P firstWitness secondWitness

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

CountPreserved :
  Signature →
  List Color →
  List Color →
  Set
CountPreserved sig original current =
  (color : Color) →
  nbOcc sig (nthColor sig current) zeroZ (lengthZ current) color ≡
  nbOcc sig (nthColor sig original) zeroZ (lengthZ current) color

Invariant :
  Signature →
  List Color →
  Int →
  Int →
  Int →
  List Color →
  Set
Invariant sig original blueEnd scan redStart current =
  ((zeroZ ≤Z blueEnd) ∧
   (blueEnd ≤Z scan) ∧
   (scan ≤Z redStart) ∧
   (redStart ≤Z lengthZ current)) ∧
  Monochrome (nthColor sig current) zeroZ blueEnd Blue ∧
  Monochrome (nthColor sig current) blueEnd scan White ∧
  Monochrome (nthColor sig current) redStart (lengthZ current) Red ∧
  CountPreserved sig original current

InitialState : Signature → List Color → Set
InitialState sig original =
  let end = lengthZ original
  in
  ((zeroZ ≤Z zeroZ) ∧
   (zeroZ ≤Z zeroZ) ∧
   (zeroZ ≤Z end) ∧
   (end ≤Z lengthZ original)) ∧
  Monochrome (nthColor sig original) zeroZ zeroZ Blue ∧
  Monochrome (nthColor sig original) zeroZ zeroZ White ∧
  Monochrome (nthColor sig original) end (lengthZ original) Red

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

CountsOnIntervalPreserved :
  Signature →
  List Color →
  List Color →
  Int →
  Int →
  Int →
  Int →
  Color →
  Set
CountsOnIntervalPreserved
  sig before after firstIndex secondIndex lower upper color =
  (((lower ≤Z firstIndex) ∧ (firstIndex <Z upper)) ∧
   (lower ≤Z secondIndex) ∧ (secondIndex <Z upper)) →
  nbOcc sig (nthColor sig after) lower upper color ≡
  nbOcc sig (nthColor sig before) lower upper color

ExchangeAt :
  Signature →
  List Color →
  List Color →
  Int →
  Int →
  Set
ExchangeAt sig before after firstIndex secondIndex =
  nthColor sig after firstIndex ≡ nthColor sig before secondIndex ∧
  nthColor sig after secondIndex ≡ nthColor sig before firstIndex ∧
  UnchangedExcept sig before after firstIndex secondIndex ∧
  ((lower upper : Int) →
   (color : Color) →
   CountsOnIntervalPreserved
     sig before after firstIndex secondIndex lower upper color)

BlueConclusion :
  Signature →
  List Color →
  Int →
  Int →
  Int →
  List Color →
  Set
BlueConclusion sig original blueEnd scan redStart after =
  ((zeroZ ≤Z subtractInt redStart scan) ∧
   (subtractInt redStart (addInt scan oneZ) <Z
    subtractInt redStart scan)) ∧
  Invariant
    sig
    original
    (addInt blueEnd oneZ)
    (addInt scan oneZ)
    redStart
    after

BlueCase :
  Signature →
  List Color →
  Int →
  Int →
  Int →
  List Color →
  Set
BlueCase sig original blueEnd scan redStart current =
  (((zeroZ ≤Z blueEnd) ∧ (blueEnd <Z lengthZ current)) ∧
   (zeroZ ≤Z scan) ∧ (scan <Z lengthZ current)) ∧
  ((after : List Color) →
   (length after ≡ length current) →
   ExchangeAt sig current after blueEnd scan →
   BlueConclusion sig original blueEnd scan redStart after)

WhiteCase :
  Signature →
  List Color →
  Int →
  Int →
  Int →
  List Color →
  Set
WhiteCase sig original blueEnd scan redStart current =
  ((zeroZ ≤Z subtractInt redStart scan) ∧
   (subtractInt redStart (addInt scan oneZ) <Z
    subtractInt redStart scan)) ∧
  Invariant
    sig
    original
    blueEnd
    (addInt scan oneZ)
    redStart
    current

RedConclusion :
  Signature →
  List Color →
  Int →
  Int →
  Int →
  List Color →
  Set
RedConclusion sig original blueEnd scan redStart after =
  ((zeroZ ≤Z subtractInt redStart scan) ∧
   (subtractInt (subtractInt redStart oneZ) scan <Z
    subtractInt redStart scan)) ∧
  Invariant
    sig
    original
    blueEnd
    scan
    (subtractInt redStart oneZ)
    after

RedCase :
  Signature →
  List Color →
  Int →
  Int →
  Int →
  List Color →
  Set
RedCase sig original blueEnd scan redStart current =
  (((zeroZ ≤Z subtractInt redStart oneZ) ∧
    (subtractInt redStart oneZ <Z lengthZ current)) ∧
   (zeroZ ≤Z scan) ∧
   (scan <Z lengthZ current)) ∧
  ((after : List Color) →
   (length after ≡ length current) →
   ExchangeAt sig current after (subtractInt redStart oneZ) scan →
   RedConclusion sig original blueEnd scan redStart after)

StepByColor :
  Signature →
  List Color →
  Int →
  Int →
  Int →
  List Color →
  Color →
  Set
StepByColor sig original blueEnd scan redStart current Blue =
  BlueCase sig original blueEnd scan redStart current
StepByColor sig original blueEnd scan redStart current White =
  WhiteCase sig original blueEnd scan redStart current
StepByColor sig original blueEnd scan redStart current Red =
  RedCase sig original blueEnd scan redStart current

LoopStep :
  Signature →
  List Color →
  Int →
  Int →
  Int →
  List Color →
  Set
LoopStep sig original blueEnd scan redStart current =
  ((zeroZ ≤Z scan) ∧ (scan <Z lengthZ current)) ∧
  StepByColor
    sig
    original
    blueEnd
    scan
    redStart
    current
    (nthColor sig current scan)

ColoredPartition :
  Signature →
  List Color →
  Set
ColoredPartition sig current =
  Exists₂ Int Int λ blueEnd redStart →
    Monochrome (nthColor sig current) zeroZ blueEnd Blue ∧
    Monochrome (nthColor sig current) blueEnd redStart White ∧
    Monochrome (nthColor sig current) redStart (lengthZ current) Red

TerminalState :
  Signature →
  List Color →
  List Color →
  Set
TerminalState sig original current =
  ColoredPartition sig current ∧
  CountPreserved sig original current

LoopBody :
  Signature →
  List Color →
  Int →
  Int →
  Int →
  List Color →
  Set
LoopBody sig original blueEnd scan redStart current =
  IfSet
    (intLess scan redStart)
    (LoopStep sig original blueEnd scan redStart current)
    (TerminalState sig original current)

DutchFlagVC : Signature → List Color → Set
DutchFlagVC sig original =
  InitialState sig original ∧
  ((redStart scan blueEnd : Int) →
   (current : List Color) →
   (length current ≡ length original) →
   Invariant sig original blueEnd scan redStart current →
   LoopBody sig original blueEnd scan redStart current)

dutch-flag'vc : Set
dutch-flag'vc =
  (sig : Signature) →
  Laws sig →
  (original : List Color) →
  DutchFlagVC sig original
