-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/klibc_stdio/__fflush_Why3_ide_VC__fflush_call_write_pre_goal31:
-- under the stated integer-range, framing, linkedness, file-validity,
-- address-order, and writable-memory assumptions for fflush, the nested
-- zero-offset integer load is nonnegative. This file contains no proof.

{-# OPTIONS --safe #-}

module fflush-Why3-ide-VC-fflush-call-write-pre-goal31 where

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

zeroZ oneZ threeZ fourZ fiveZ sixZ sevenZ eightZ nineZ elevenZ
  thirtyTwoZ sixteenThousandThreeHundredEightyFourZ : Int
zeroZ = pos zero
oneZ = pos 1
threeZ = pos 3
fourZ = pos 4
fiveZ = pos 5
sixZ = pos 6
sevenZ = pos 7
eightZ = pos 8
nineZ = pos 9
elevenZ = pos 11
thirtyTwoZ = pos 32
sixteenThousandThreeHundredEightyFourZ = pos 16384

negativeOneZ signed32Lower signed32Upper uint32Upper : Int
negativeOneZ = negsuc zero
signed32Lower = negsuc 2147483647
signed32Upper = pos 2147483648
uint32Upper = pos 4294967296

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

shift : Addr → Int → Addr
shift p k = addr (base p) (addInt (offset p) k)

record AddressOrder : Set₁ where
  field
    addrLE     : Addr → Addr → Set
    addrLT     : Addr → Addr → Set
    addrLEBool : Addr → Addr → Bool
    addrLTBool : Addr → Addr → Bool

    addrLE-same-base :
      (p q : Addr) →
      base p ≡ base q →
      Iff (addrLE p q) (offset p ≤Z offset q)

    addrLT-same-base :
      (p q : Addr) →
      base p ≡ base q →
      Iff (addrLT p q) (offset p <Z offset q)

    addrLE-boolean :
      (p q : Addr) →
      Iff (addrLE p q) (addrLEBool p q ≡ true)

    addrLT-boolean :
      (p q : Addr) →
      Iff (addrLT p q) (addrLTBool p q ≡ true)

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

Framed : (Int → Int) → (Addr → Addr) → Set
Framed region pointerMemory =
  (p : Addr) →
  region (base (pointerMemory p)) ≤Z zeroZ

IsUint32 : Int → Set
IsUint32 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint32Upper)

IsSint32 : Int → Set
IsSint32 x =
  (signed32Lower ≤Z x) ∧
  (x <Z signed32Upper)

PValidFile :
  (Int → Int) →
  (Addr → Int) →
  Addr →
  Set
PValidFile allocation integerMemory file =
  (zeroZ ≤Z integerMemory (shift file zeroZ)) ∧
  ValidRW allocation file threeZ

PValidIOFilePvtNoRec :
  AddressOrder →
  (Int → Int) →
  (Addr → Addr) →
  (Addr → Int) →
  Addr →
  Set
PValidIOFilePvtNoRec order allocation pointerMemory integerMemory file =
  let
    x = integerMemory (shift file nineZ)
    x₁ = integerMemory (shift file sevenZ)
    x₂ = integerMemory (shift file eightZ)
    a = pointerMemory (shift file fiveZ)
    a₁ = pointerMemory (shift file sixZ)
    a₂ = pointerMemory (shift file fourZ)
    a₃ = pointerMemory (shift file threeZ)
    a₄ = shift a zeroZ
    x₃ = addInt thirtyTwoZ x
  in
  (x ≡ sixteenThousandThreeHundredEightyFourZ) ∧
  (zeroZ ≤Z x₁) ∧
  (x₁ <Z x) ∧
  (zeroZ ≤Z x₂) ∧
  (x₂ <Z x) ∧
  ValidRW allocation file elevenZ ∧
  addrLE order a a₁ ∧
  PValidFile allocation integerMemory (shift file zeroZ) ∧
  ValidRW allocation a₂ elevenZ ∧
  ValidRW allocation a₃ elevenZ ∧
  Separated file elevenZ a₂ elevenZ ∧
  Separated file elevenZ a₃ elevenZ ∧
  Separated a₂ elevenZ a₃ elevenZ ∧
  ValidRW allocation a₄ x₃ ∧
  Separated file elevenZ a₄ x₃ ∧
  Separated a₂ elevenZ a₄ x₃ ∧
  Separated a₃ elevenZ a₄ x₃ ∧
  addrLT order a₁ (shift a x₃)

PValidIOFilePvt :
  AddressOrder →
  (Int → Int) →
  (Addr → Addr) →
  (Addr → Int) →
  Addr →
  Set
PValidIOFilePvt order allocation pointerMemory integerMemory file =
  let
    x = integerMemory (shift file nineZ)
    a = pointerMemory (shift file sixZ)
    a₁ = pointerMemory (shift file fiveZ)
    a₂ = pointerMemory (shift file threeZ)
    a₃ = pointerMemory (shift file fourZ)
    x₁ = integerMemory (shift file sevenZ)
    x₂ = integerMemory (shift file eightZ)
    a₄ = shift a₁ zeroZ
    x₃ = addInt thirtyTwoZ x
  in
  (x ≡ sixteenThousandThreeHundredEightyFourZ) ∧
  (base a ≡ base a₁) ∧
  (pointerMemory (shift a₂ fourZ) ≡ file) ∧
  (pointerMemory (shift a₃ threeZ) ≡ file) ∧
  (zeroZ ≤Z x₁) ∧
  (x₁ <Z x) ∧
  (zeroZ ≤Z x₂) ∧
  (x₂ <Z x) ∧
  ValidRW allocation file elevenZ ∧
  addrLE order a₁ a ∧
  PValidFile allocation integerMemory (shift file zeroZ) ∧
  Separated file elevenZ a₃ elevenZ ∧
  Separated file elevenZ a₂ elevenZ ∧
  Separated a₃ elevenZ a₂ elevenZ ∧
  PValidIOFilePvtNoRec order allocation pointerMemory integerMemory a₃ ∧
  PValidIOFilePvtNoRec order allocation pointerMemory integerMemory a₂ ∧
  ValidRW allocation a₄ x₃ ∧
  Separated file elevenZ a₄ x₃ ∧
  Separated a₃ elevenZ a₄ x₃ ∧
  Separated a₂ elevenZ a₄ x₃ ∧
  addrLT order a (shift a₁ x₃)

Goal31 :
  AddressOrder →
  (Int → Int) →
  ((Int → Int) → Set) →
  Set
Goal31 order region linked =
  (pointerMemory : Addr → Addr) →
  (file resultBuffer : Addr) →
  (integerMemory : Addr → Int) →
  (byteCount result : Int) →
  (allocation : Int → Int) →
  let
    buffer = pointerMemory (shift file fiveZ)
    bufferBase = base buffer
    resultBase = base resultBuffer
    endBufferBase = base (pointerMemory (shift file sixZ))
    bufferSize = integerMemory (shift file nineZ)
    nestedValue =
      integerMemory (shift (shift file zeroZ) zeroZ)
  in
  byteCount ≠ zeroZ →
  integerMemory (shift file sevenZ) ≡ zeroZ →
  bufferBase ≡ resultBase →
  endBufferBase ≡ resultBase →
  endBufferBase ≡ bufferBase →
  zeroZ ≤Z byteCount →
  result ≤Z byteCount →
  region (base file) ≤Z zeroZ →
  negativeOneZ ≤Z result →
  Framed region pointerMemory →
  linked allocation →
  IsUint32 byteCount →
  IsSint32 result →
  IsUint32 bufferSize →
  IsUint32 (integerMemory (shift file eightZ)) →
  PValidIOFilePvt order allocation pointerMemory integerMemory file →
  addrLE order buffer resultBuffer →
  ValidRW allocation (shift resultBuffer zeroZ) byteCount →
  IsSint32 nestedValue →
  addrLE order
    resultBuffer
    (shift buffer (addInt thirtyTwoZ bufferSize)) →
  zeroZ ≤Z nestedValue

fflush-call-write-pre-goal31 : Set₁
fflush-call-write-pre-goal31 =
  (order : AddressOrder) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  Goal31 order region linked
