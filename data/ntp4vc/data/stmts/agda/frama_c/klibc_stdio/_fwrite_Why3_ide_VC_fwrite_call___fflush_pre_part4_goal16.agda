-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/klibc_stdio/_fwrite_Why3_ide_VC_fwrite_call___fflush_pre_part4_goal16:
-- preservation of the private FILE validity predicate after three integer-memory
-- updates, under the stated uint32-range, memory, framing, linkedness, constancy,
-- interval-exclusion, and writable-memory assumptions. This file contains no proof.

{-# OPTIONS --safe #-}

module FwriteWhy3IdeVCFwriteCallFflushPrePart4Goal16 where

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

andBool : Bool → Bool → Bool
andBool true value = value
andBool false _ = false

ifBool : {A : Set} → Bool → A → A → A
ifBool true yes _ = yes
ifBool false _ no = no

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

zeroZ oneZ twoZ threeZ fourZ fiveZ sixZ sevenZ eightZ nineZ tenZ elevenZ
  thirtyTwoZ sixteenThousandThreeHundredEightyThreeZ
  sixteenThousandThreeHundredEightyFourZ
  sixteenThousandFourHundredSixteenZ : Int
zeroZ = pos zero
oneZ = pos 1
twoZ = pos 2
threeZ = pos 3
fourZ = pos 4
fiveZ = pos 5
sixZ = pos 6
sevenZ = pos 7
eightZ = pos 8
nineZ = pos 9
tenZ = pos 10
elevenZ = pos 11
thirtyTwoZ = pos 32
sixteenThousandThreeHundredEightyThreeZ = pos 16383
sixteenThousandThreeHundredEightyFourZ = pos 16384
sixteenThousandFourHundredSixteenZ = pos 16416

uint32Upper : Int
uint32Upper = pos 4294967296

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

shift : Addr → Int → Addr
shift p k = addr (base p) (addInt (offset p) k)

addrEqual : Addr → Addr → Bool
addrEqual p q =
  andBool
    (intEqual (base p) (base q))
    (intEqual (offset p) (offset q))

update : {A : Set} → (Addr → A) → Addr → A → Addr → A
update memory location value query =
  ifBool (addrEqual query location) value (memory query)

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

record Uint32Projection : Set where
  field
    toUint32 : Int → Int

    toUint32-in-range :
      (x : Int) →
      IsUint32 (toUint32 x)

    toUint32-identity :
      (x : Int) →
      IsUint32 x →
      toUint32 x ≡ x

open Uint32Projection

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

Goal16 :
  AddressOrder →
  Uint32Projection →
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal16 order conversion region linked sconst =
  (i₃ i₄ : Int) →
  (a₄ a₅ a₂ a : Addr) →
  (t₁ t₂ : Addr → Int) →
  (i₅ : Int) →
  (t₃ : Addr → Addr) →
  (t : Int → Int) →
  (a₁ a₃ : Addr) →
  (i i₁ i₂ : Int) →
  let
    x = addInt i₃ i₄
    dataPointer = t₃ (shift a₅ sixZ)
    bufferPointer = t₃ (shift a₅ fiveZ)
    previousFile = t₃ (shift a₅ fourZ)
    nextFile = t₃ (shift a₅ threeZ)
    inputBytes = t₁ (shift a₅ sevenZ)
    writeStart = shift a₄ zeroZ
    bufferStart = shift bufferPointer zeroZ
    publicFile = shift a₅ zeroZ
    updatedIntegerMemory =
      update
        (update
          (update t₁ (shift a₅ eightZ) i)
          (shift publicFile oneZ)
          i₁)
        (shift publicFile twoZ)
        i₂
  in
  i₄ ≠ zeroZ →
  shift a₂ zeroZ ≡ shift a zeroZ →
  t₁ (shift a₅ tenZ) ≡ oneZ →
  t₁ (shift a₅ nineZ) ≡ sixteenThousandThreeHundredEightyFourZ →
  base dataPointer ≡ base bufferPointer →
  t₃ (shift previousFile threeZ) ≡ a₅ →
  t₃ (shift nextFile fourZ) ≡ a₅ →
  t₂
    (shift a₄
      (toUint32 conversion (subtractInt i₄ oneZ)))
    ≡
  tenZ →
  zeroZ ≤Z i →
  zeroZ ≤Z i₃ →
  zeroZ ≤Z i₄ →
  zeroZ ≤Z i₅ →
  zeroZ ≤Z x →
  zeroZ ≤Z inputBytes →
  region (base a₂) ≤Z zeroZ →
  region (base a₄) ≤Z zeroZ →
  i ≤Z sixteenThousandThreeHundredEightyThreeZ →
  inputBytes ≤Z sixteenThousandThreeHundredEightyThreeZ →
  Framed region t₃ →
  linked t →
  sconst t₂ →
  IsUint32 i →
  IsUint32 i₃ →
  IsUint32 i₄ →
  IsUint32 i₅ →
  ValidRW t a₅ elevenZ →
  IsUint32 x →
  IsUint32 inputBytes →
  PValidIOFilePvt order t t₃ t₁ a₁ →
  PValidIOFilePvt order t t₃ t₁ a₃ →
  PValidIOFilePvt order t t₃ t₁ a₅ →
  addrLE order bufferPointer dataPointer →
  ValidRW t writeStart i₄ →
  ValidRW t writeStart x →
  Separated a₅ elevenZ nextFile elevenZ →
  Separated a₅ elevenZ previousFile elevenZ →
  Separated nextFile elevenZ previousFile elevenZ →
  addrLT
    order
    dataPointer
    (shift bufferPointer sixteenThousandFourHundredSixteenZ) →
  ValidRW t bufferStart sixteenThousandFourHundredSixteenZ →
  PValidFile t updatedIntegerMemory publicFile →
  Separated
    a₅
    elevenZ
    bufferStart
    sixteenThousandFourHundredSixteenZ →
  Separated
    nextFile
    elevenZ
    bufferStart
    sixteenThousandFourHundredSixteenZ →
  Separated
    previousFile
    elevenZ
    bufferStart
    sixteenThousandFourHundredSixteenZ →
  PValidIOFilePvtNoRec
    order
    t
    t₃
    updatedIntegerMemory
    nextFile →
  PValidIOFilePvtNoRec
    order
    t
    t₃
    updatedIntegerMemory
    previousFile →
  ((i₆ : Int) →
    i₄ <Z i₆ →
    i₆ ≤Z x →
    t₂ (shift a₄ (subtractInt i₆ oneZ)) ≠ tenZ) →
  PValidIOFilePvt order t t₃ updatedIntegerMemory a₅

fwrite-call-fflush-pre-part4-goal16 : Set₁
fwrite-call-fflush-pre-part4-goal16 =
  (order : AddressOrder) →
  (conversion : Uint32Projection) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal16 order conversion region linked sconst
