-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/verker/strchr_Why3_ide_VCstrchr_assert_goal7: the strchr assertion
-- verification condition relating address order before the string terminator
-- to the searched signed byte being nonzero, under the stated memory-model,
-- integer-range, string-validity, linkedness, and constancy assumptions.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module strchr_Why3_ide_VCstrchr_assert_goal7 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≠_ _≤Z_ _<Z_
infixr 3 _∧_
infix 2 _↔_

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

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record _↔_ (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A → B
    backward : B → A

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

zeroZ oneZ signedByteUpper signed32Upper uint64Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
signedByteUpper = pos 128
signed32Upper = pos 2147483648
uint64Upper = pos 18446744073709551616

signedByteLower signed32Lower : Int
signedByteLower = negsuc 127
signed32Lower = negsuc 2147483647

IsSint8 : Int → Set
IsSint8 x =
  (signedByteLower ≤Z x) ∧
  (x <Z signedByteUpper)

IsSint32 : Int → Set
IsSint32 x =
  (signed32Lower ≤Z x) ∧
  (x <Z signed32Upper)

IsUint64 : Int → Set
IsUint64 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint64Upper)

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

shift : Addr → Int → Addr
shift p k = addr (base p) (addInt (offset p) k)

nullAddr : Addr
nullAddr = addr zeroZ zeroZ

ValidRW : (Int → Int) → Addr → Int → Set
ValidRW allocation p n =
  zeroZ <Z n →
  (zeroZ <Z base p) ∧
  (zeroZ ≤Z offset p) ∧
  (addInt (offset p) n ≤Z allocation (base p))

record AddressOrderModel : Set₁ where
  field
    addrLE : Addr → Addr → Set
    addrLT : Addr → Addr → Set

    addrLE-on-common-base :
      (p q : Addr) →
      base p ≡ base q →
      addrLE p q ↔ (offset p ≤Z offset q)

    addrLT-on-common-base :
      (p q : Addr) →
      base p ≡ base q →
      addrLT p q ↔ (offset p <Z offset q)

open AddressOrderModel

record CIntegerProjection : Set where
  field
    toSint8  : Int → Int
    toUint64 : Int → Int

    toSint8-in-range :
      (x : Int) →
      IsSint8 (toSint8 x)

    toUint64-in-range :
      (x : Int) →
      IsUint64 (toUint64 x)

    toSint8-identity :
      (x : Int) →
      IsSint8 x →
      toSint8 x ≡ x

    toUint64-identity :
      (x : Int) →
      IsUint64 x →
      toUint64 x ≡ x

open CIntegerProjection

record StringLengthModel (integers : CIntegerProjection) : Set where
  field
    lStrlen : (Addr → Int) → Addr → Int

    lStrlen-equation :
      (scalarMemory : Addr → Int) →
      (string : Addr) →
      Either
        ((scalarMemory (shift string zeroZ) ≡ zeroZ) ∧
         (lStrlen scalarMemory string ≡ zeroZ))
        ((scalarMemory (shift string zeroZ) ≠ zeroZ) ∧
         (toUint64 integers
           (addInt oneZ
             (lStrlen scalarMemory (shift string oneZ)))
          ≡ lStrlen scalarMemory string))

    lStrlen-in-range :
      (scalarMemory : Addr → Int) →
      (string : Addr) →
      IsUint64 (lStrlen scalarMemory string)

open StringLengthModel

record StringSearchModel : Set where
  field
    lStrchr : (Addr → Int) → Addr → Int → Addr

    lStrchr-equation :
      (scalarMemory : Addr → Int) →
      (string : Addr) →
      (character : Int) →
      Either
        ((scalarMemory string ≡ character) ∧
         (lStrchr scalarMemory string character ≡ string))
        ((scalarMemory string ≠ character) ∧
         Either
           ((scalarMemory string ≡ zeroZ) ∧
            (lStrchr scalarMemory string character ≡ nullAddr))
           ((scalarMemory string ≠ zeroZ) ∧
            (lStrchr scalarMemory (shift string oneZ) character
             ≡ lStrchr scalarMemory string character)))

open StringSearchModel

PValidString :
  (Int → Int) →
  (Addr → Int) →
  Addr →
  Set
PValidString allocation scalarMemory string =
  Exists Int
    (λ terminator →
      (scalarMemory (shift string terminator) ≡ zeroZ) ∧
      IsUint64 terminator ∧
      ValidRW allocation
        (shift string zeroZ)
        (addInt oneZ terminator) ∧
      ((index : Int) →
        index ≤Z terminator →
        IsSint8 (scalarMemory (shift string index))))

Goal7 :
  (integers : CIntegerProjection) →
  StringLengthModel integers →
  StringSearchModel →
  AddressOrderModel →
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal7 integers lengths search order region linked sconst =
  (scalarMemory : Addr → Int) →
  (a a₁ : Addr) →
  (i : Int) →
  (allocation : Int → Int) →
  let
    x = scalarMemory a
    a₂ = shift a₁ (lStrlen lengths scalarMemory a₁)
  in
  x ≡ toSint8 integers i →
  lStrchr search scalarMemory a₁ x
    ≡ lStrchr search scalarMemory a x →
  region (base a₁) ≤Z zeroZ →
  linked allocation →
  sconst scalarMemory →
  IsSint32 i →
  addrLE order a₁ a →
  IsSint8 x →
  PValidString allocation scalarMemory a →
  PValidString allocation scalarMemory a₁ →
  addrLE order a a₂ →
  ((a₃ : Addr) →
    addrLT order a₃ a →
    addrLE order a₁ a₃ →
    x ≠ scalarMemory a₃) →
  addrLT order a a₂ ↔ (x ≠ zeroZ)

strchr-assert-goal7 : Set₁
strchr-assert-goal7 =
  (integers : CIntegerProjection) →
  (lengths : StringLengthModel integers) →
  (search : StringSearchModel) →
  (order : AddressOrderModel) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal7 integers lengths search order region linked sconst
