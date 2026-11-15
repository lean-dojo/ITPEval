-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/klibc_string/strcat_Why3_ide_VCstrcat_call_strcpy_pre_6_goal9:
-- the strcat verification condition asserting separation of the destination
-- and the selected source ranges before strcpy, under the stated memory-validity,
-- string-length, character-occurrence, and address-order assumptions. This
-- file contains no proof.

{-# OPTIONS --safe #-}

module strcat-Why3-ide-VCstrcat-call-strcpy-pre-6-goal9 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≠_ _≤Z_ _<Z_
infixr 3 _∧_

data Bottom : Set where

Not : Set → Set
Not proposition = proposition → Bottom

_≠_ : {A : Set} → A → A → Set
x ≠ y = Not (x ≡ y)

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A → B
    backward : B → A

record Exists (P : Int → Set) : Set where
  constructor witness
  field
    value    : Int
    evidence : P value

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

zeroZ oneZ signedByteLower signedByteUpper signedByteExclusiveUpper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
signedByteLower = negsuc 127
signedByteUpper = pos 127
signedByteExclusiveUpper = pos 128

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

shift : Addr → Int → Addr
shift p k = addr (base p) (addInt (offset p) k)

zeroAddr : Addr
zeroAddr = addr zeroZ zeroZ

record AddressOrder : Set₁ where
  field
    addrLE     : Addr → Addr → Set
    addrLEBool : Addr → Addr → Bool

    addrLE-same-base :
      (p q : Addr) →
      base p ≡ base q →
      Iff (addrLE p q) (offset p ≤Z offset q)

    addrLE-boolean :
      (p q : Addr) →
      Iff (addrLE p q) (addrLEBool p q ≡ true)

open AddressOrder

ValidRW : (Int → Int) → Addr → Int → Set
ValidRW allocation p n =
  zeroZ <Z n →
  (zeroZ <Z base p) ∧
  (zeroZ ≤Z offset p) ∧
  (addInt (offset p) n ≤Z allocation (base p))

Separated : Addr → Int → Addr → Int → Set
Separated p a q b =
  Either
    (a ≤Z zeroZ)
    (Either
      (b ≤Z zeroZ)
      (Either
        (base p ≠ base q)
        (Either
          (addInt (offset q) b ≤Z offset p)
          (addInt (offset p) a ≤Z offset q))))

IsSint8 : Int → Set
IsSint8 x =
  (signedByteLower ≤Z x) ∧
  (x <Z signedByteExclusiveUpper)

record CIntegerProjection : Set where
  field
    toSint8 : Int → Int

    toSint8-in-range :
      (x : Int) →
      IsSint8 (toSint8 x)

    toSint8-identity :
      (x : Int) →
      IsSint8 x →
      toSint8 x ≡ x

open CIntegerProjection

PLengthOfStrIs :
  (Int → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Set
PLengthOfStrIs allocation memory string n =
  (memory (shift string n) ≡ zeroZ) ∧
  (zeroZ ≤Z n) ∧
  ValidRW allocation (shift string zeroZ) (addInt oneZ n) ∧
  ((index : Int) →
    zeroZ ≤Z index →
    index <Z n →
    memory (shift string index) ≠ zeroZ)

record StringLength : Set where
  field
    length : (Addr → Int) → Addr → Int

    length-of-string :
      (allocation : Int → Int) →
      (memory : Addr → Int) →
      (string : Addr) →
      (n : Int) →
      PLengthOfStrIs allocation memory string n →
      length memory string ≡ n

open StringLength

PExistsFirstOccurrenceOfChar :
  CIntegerProjection →
  StringLength →
  (Int → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Set
PExistsFirstOccurrenceOfChar projection lengths allocation memory string c position =
  let
    character = toSint8 projection c
    stringLength = length lengths memory string
  in
  (memory (shift string position) ≡ character) ∧
  (zeroZ ≤Z position) ∧
  (position ≤Z stringLength) ∧
  (signedByteLower ≤Z c) ∧
  (c ≤Z signedByteUpper) ∧
  ValidRW allocation
    (shift string zeroZ)
    (addInt oneZ stringLength) ∧
  ((index : Int) →
    zeroZ ≤Z index →
    index <Z position →
    memory (shift string index) ≠ character)

OccursBefore :
  (Addr → Int) →
  Addr →
  Int →
  Set
OccursBefore memory string bound =
  Exists λ index →
    (memory (shift string index) ≡ zeroZ) ∧
    (zeroZ ≤Z index) ∧
    (index <Z bound)

NoZeroBefore :
  (Addr → Int) →
  Addr →
  Int →
  Set
NoZeroBefore memory string bound =
  (index : Int) →
  zeroZ ≤Z index →
  index <Z bound →
  memory (shift string index) ≠ zeroZ

Goal9 :
  AddressOrder →
  CIntegerProjection →
  StringLength →
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal9 order projection lengths region linked sconst =
  (a₂ : Addr) →
  (memory : Addr → Int) →
  (a : Addr) →
  (a₁ : Addr) →
  (allocation : Int → Int) →
  (i i₃ i₁ i₂ i₄ : Int) →
  let
    x = base a₂
    x₁ = memory a
    a₃ = shift a₂ zeroZ
    x₂ = length lengths memory a₁
    x₃ = length lengths memory a₂
    a₄ = shift a₁ zeroZ
    x₄ = addInt oneZ x₂
    zeroOccurs = OccursBefore memory a₂ x₃
  in
  region (base a₁) ≤Z zeroZ →
  region x ≤Z zeroZ →
  linked allocation →
  sconst memory →
  IsSint8 x₁ →
  PLengthOfStrIs allocation memory a₁ i →
  PLengthOfStrIs allocation memory a₁ i₃ →
  PLengthOfStrIs allocation memory a₂ i₁ →
  PLengthOfStrIs allocation memory a₂ i₂ →
  PLengthOfStrIs allocation memory a₂ i₄ →
  ValidRW allocation a₃ (addInt x₂ x₃) →
  Separated a₃ (addInt oneZ x₃) a₄ x₄ →
  (NoZeroBefore memory a₂ x₃ → zeroAddr ≡ a) →
  (zeroOccurs → x₁ ≡ zeroZ) →
  (zeroOccurs → x ≡ base a) →
  (zeroOccurs →
    PExistsFirstOccurrenceOfChar
      projection
      lengths
      allocation
      memory
      a₂
      zeroZ
      (subtractInt (offset a) (offset a₂))) →
  (zeroOccurs →
    addrLE order a₂ a ∧
    addrLE order a (shift a₂ x₃)) →
  Separated a₄ x₄ (shift a zeroZ) x₄

strcat-call-strcpy-pre-6-goal9 : Set₁
strcat-call-strcpy-pre-6-goal9 =
  (order : AddressOrder) →
  (projection : CIntegerProjection) →
  (lengths : StringLength) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal9 order projection lengths region linked sconst
