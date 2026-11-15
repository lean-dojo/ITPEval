-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_not_newly_idle_with_idle_cpu_post_2_goal39:
-- under the stated integer-range, memory-validity, separation, framing,
-- linkedness, CPU-mask, havoc-update, and scheduler-loop assumptions, the
-- selected CPU equals i6 exactly when the boolean result i2 is nonzero.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module should-we-balance-Why3-ide-VCshould-we-balance-not-newly-idle-with-idle-cpu-post-2-goal39 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _≤Z_ _<Z_ _↔_
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

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
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

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) = negative (m * suc n)
multiplyInt (negsuc m) (pos n) = negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) = pos (suc m * suc n)

zeroZ oneZ twoZ threeZ fourZ fiveZ eightZ minusOneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos 2
threeZ = pos 3
fourZ = pos 4
fiveZ = pos 5
eightZ = pos 8
minusOneZ = negsuc zero

uint8Upper uint32Upper : Int
uint8Upper = pos 256
uint32Upper = pos 4294967296

signed32Lower signed32Upper signed32Maximum : Int
signed32Lower = negsuc 2147483647
signed32Upper = pos 2147483648
signed32Maximum = pos 2147483647

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

shift : Addr → Int → Addr
shift p k = addr (base p) (addInt (offset p) k)

ValidRW : (Int → Int) → Addr → Int → Set
ValidRW allocation p n =
  zeroZ <Z n →
  (zeroZ <Z base p) ∧
  (zeroZ ≤Z offset p) ∧
  (addInt (offset p) n ≤Z allocation (base p))

ValidRD : (Int → Int) → Addr → Int → Set
ValidRD allocation p n =
  zeroZ <Z n →
  (zeroZ ≠ base p) ∧
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
Framed region pointer-memory =
  (p : Addr) →
  region (base (pointer-memory p)) ≤Z zeroZ

IsUint8 : Int → Set
IsUint8 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint8Upper)

IsUint32 : Int → Set
IsUint32 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint32Upper)

IsSint32 : Int → Set
IsSint32 x =
  (signed32Lower ≤Z x) ∧
  (x <Z signed32Upper)

CongruentModulo : Int → Int → Int → Set
CongruentModulo modulus x y =
  Exists Int λ multiple →
    x ≡ addInt y (multiplyInt multiple modulus)

record Uint32Projection : Set where
  field
    toUint32 : Int → Int

    toUint32-in-range :
      (x : Int) →
      IsUint32 (toUint32 x)

    toUint32-congruent :
      (x : Int) →
      CongruentModulo uint32Upper x (toUint32 x)

open Uint32Projection

record HavocTheory : Set where
  field
    havoc :
      (Addr → Int) →
      (Addr → Int) →
      Addr →
      Int →
      Addr →
      Int

    havoc-separated :
      (memory₀ memory₁ : Addr → Int) →
      (start : Addr) →
      (length : Int) →
      (location : Addr) →
      Separated location oneZ start length →
      havoc memory₀ memory₁ start length location ≡ memory₁ location

    havoc-overwritten :
      (memory₀ memory₁ : Addr → Int) →
      (start : Addr) →
      (length : Int) →
      (location : Addr) →
      Not (Separated location oneZ start length) →
      havoc memory₀ memory₁ start length location ≡ memory₀ location

open HavocTheory

DivisibleByEight : Int → Set
DivisibleByEight x =
  Exists Int λ multiple →
    x ≡ multiplyInt eightZ multiple

LandSevenNonzero : Int → Set
LandSevenNonzero x = Not (DivisibleByEight x)

HasActiveFrom :
  (Addr → Int) →
  Addr →
  Addr →
  Int →
  Int →
  Set
HasActiveFrom integer-memory first-mask second-mask lower upper =
  Exists Int λ index →
    integer-memory (shift first-mask index) ≠ zeroZ ∧
    integer-memory (shift second-mask index) ≠ zeroZ ∧
    index <Z upper ∧
    lower ≤Z index

IdleCore :
  Int →
  (Int → Int) →
  (Int → Addr) →
  (Addr → Addr) →
  (Addr → Int) →
  Int →
  Set
IdleCore lSize lIdleCpu lCpuSmtMask pointer-memory integer-memory cpu =
  (index : Int) →
  integer-memory
    (shift
      (pointer-memory (shift (lCpuSmtMask cpu) zeroZ))
      index) ≠ zeroZ →
  zeroZ ≤Z index →
  index <Z lSize →
  lIdleCpu index ≠ zeroZ

record CpuMaskTheory
  (lSize : Int)
  (lIdleCpu : Int → Int)
  (lCpuSmtMask : Int → Addr)
  : Set where
  field
    idleCpuUint8 :
      (cpu : Int) →
      IsUint8 (lIdleCpu cpu)

    maskRefl :
      (index : Int) →
      (integer-memory : Addr → Int) →
      (pointer-memory : Addr → Addr) →
      zeroZ ≤Z index →
      index <Z lSize →
      integer-memory
        (shift
          (pointer-memory (shift (lCpuSmtMask index) zeroZ))
          index) ≠ zeroZ

    maskSymm :
      (integer-memory : Addr → Int) →
      (pointer-memory : Addr → Addr) →
      (j i : Int) →
      integer-memory
        (shift
          (pointer-memory (shift (lCpuSmtMask j) zeroZ))
          i) ≠ zeroZ →
      zeroZ ≤Z i →
      i <Z lSize →
      zeroZ ≤Z j →
      j <Z lSize →
      integer-memory
        (shift
          (pointer-memory (shift (lCpuSmtMask i) zeroZ))
          j) ≠ zeroZ

    maskTrans :
      (pointer-memory : Addr → Addr) →
      (i : Int) →
      (integer-memory : Addr → Int) →
      (j k : Int) →
      integer-memory
        (shift
          (pointer-memory (shift (lCpuSmtMask i) zeroZ))
          j) ≠ zeroZ →
      integer-memory
        (shift
          (pointer-memory (shift (lCpuSmtMask j) zeroZ))
          k) ≠ zeroZ →
      zeroZ ≤Z i →
      i <Z lSize →
      zeroZ ≤Z j →
      j <Z lSize →
      zeroZ ≤Z k →
      k <Z lSize →
      integer-memory
        (shift
          (pointer-memory (shift (lCpuSmtMask i) zeroZ))
          k) ≠ zeroZ

FunctionEqual : (Int → Int) → (Int → Int) → Set
FunctionEqual f g = (x : Int) → f x ≡ g x

Conditional : Set → Set → Set → Set
Conditional condition then-branch else-branch =
  Either
    (condition ∧ then-branch)
    (Not condition ∧ else-branch)

IndicatorEquals : Int → Int → Int → Set
IndicatorEquals value selected result =
  Conditional
    (value ≡ selected)
    (oneZ ≡ result)
    (zeroZ ≡ result)

ArrayStorageInvariant :
  (Int → Int) →
  (Addr → Addr) →
  Addr →
  Int →
  Int →
  Set
ArrayStorageInvariant allocation pointer-memory array length bound =
  (index : Int) →
  let current = shift array index
  in
  zeroZ ≤Z index →
  index <Z bound →
  ValidRD allocation current oneZ ∧
  ValidRW
    allocation
    (shift
      (pointer-memory (shift current zeroZ))
      zeroZ)
    length

MaskStorageInvariant :
  (Int → Int) →
  (Addr → Addr) →
  Addr →
  Int →
  (Addr → Addr) →
  Set
MaskStorageInvariant allocation pointer-memory array length mask-function =
  (address : Addr) →
  let
    mask = mask-function address
    contents =
      shift
        (pointer-memory (shift mask zeroZ))
        zeroZ
  in
  ValidRD allocation mask oneZ ∧
  ValidRD allocation contents length ∧
  ((index : Int) →
    zeroZ ≤Z index →
    index <Z length →
    Separated
      contents
      length
      (shift
        (pointer-memory (shift (shift array index) zeroZ))
        zeroZ)
      length)

CpuSmtStorageInvariant :
  (Int → Int) →
  (Addr → Addr) →
  Addr →
  Int →
  (Int → Addr) →
  Set
CpuSmtStorageInvariant allocation pointer-memory array length lCpuSmtMask =
  (index : Int) →
  let
    mask = lCpuSmtMask index
    contents =
      shift
        (pointer-memory (shift mask zeroZ))
        zeroZ
  in
  zeroZ ≤Z index →
  index <Z length →
  ValidRD allocation mask oneZ ∧
  ValidRD allocation contents length ∧
  ((other-index : Int) →
    zeroZ ≤Z other-index →
    other-index <Z length →
    Separated
      contents
      length
      (shift
        (pointer-memory (shift (shift array other-index) zeroZ))
        zeroZ)
      length)

ThenState :
  HavocTheory →
  Int →
  (Int → Int) →
  (Addr → Addr) →
  (Addr → Addr) →
  (Addr → Addr) →
  (Int → Addr) →
  Addr →
  Addr →
  Addr →
  Addr →
  Addr →
  (Addr → Int) →
  (Addr → Int) →
  (Addr → Addr) →
  (Int → Int) →
  (Int → Int) →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Set
ThenState
  havoc-theory
  lSize
  lIdleCpu
  lSchedGroupCpus
  lSchedGroupMask
  lGroupBalanceMask
  lCpuSmtMask
  array
  a₃
  a₅
  a₁₀
  a₁₈
  source-memory
  integer-memory
  pointer-memory
  allocation
  allocation₄
  i₁
  i₂
  i₈
  i₁₀
  a₂₇
  a₂₅ =
  i₁₀ ≡ i₈ ∧
  FunctionEqual allocation₄ allocation ∧
  lIdleCpu i₁₀ ≠ zeroZ ∧
  IndicatorEquals a₂₇ i₁₀ i₂ ∧
  zeroZ ≤Z i₁₀ ∧
  i₁₀ <Z lSize ∧
  ValidRD allocation₄ a₁₀ oneZ ∧
  ValidRD allocation₄ a₃ oneZ ∧
  ValidRD allocation₄ a₅ oneZ ∧
  Either
    (LandSevenNonzero a₂₅)
    (lSize ≡ i₁ ∧
      IdleCore
        lSize
        lIdleCpu
        lCpuSmtMask
        pointer-memory
        (havoc havoc-theory source-memory integer-memory a₁₈ i₁)
        i₁₀ ∧
      ArrayStorageInvariant allocation₄ pointer-memory array i₁ i₁ ∧
      MaskStorageInvariant
        allocation₄ pointer-memory array i₁ lSchedGroupCpus ∧
      MaskStorageInvariant
        allocation₄ pointer-memory array i₁ lSchedGroupMask ∧
      MaskStorageInvariant
        allocation₄ pointer-memory array i₁ lGroupBalanceMask ∧
      CpuSmtStorageInvariant
        allocation₄ pointer-memory array i₁ lCpuSmtMask)

ElseState :
  (Addr → Int) →
  Addr →
  Int →
  (Int → Int) →
  (Int → Int) →
  (Int → Int) →
  (Int → Int) →
  Int →
  Int →
  Int →
  Int →
  Addr →
  Set
ElseState
  lGroupBalanceCpu
  a₁₂
  a₂₇
  allocation
  allocation₁
  allocation₂
  allocation₃
  i₂
  i₃
  i₄
  i₇
  a₁₀ =
  i₄ ≡ i₃ ∧
  FunctionEqual allocation₁ allocation ∧
  Conditional
    (i₄ ≡ minusOneZ)
    (FunctionEqual allocation₂ allocation₁ ∧
      lGroupBalanceCpu a₁₂ ≡ i₇ ∧
      IndicatorEquals a₂₇ i₇ i₂ ∧
      ValidRD allocation₂ a₁₀ oneZ)
    (FunctionEqual allocation₃ allocation₁ ∧
      IndicatorEquals a₂₇ i₄ i₂ ∧
      ValidRD allocation₃ a₁₀ oneZ)

Goal39 :
  Uint32Projection →
  HavocTheory →
  Int →
  (Int → Int) →
  (Addr → Addr) →
  (Addr → Addr) →
  (Addr → Addr) →
  (Addr → Int) →
  (Int → Addr) →
  (Int → Int) →
  ((Int → Int) → Set) →
  Set
Goal39
  conversion
  havoc-theory
  lSize
  lIdleCpu
  lSchedGroupCpus
  lSchedGroupMask
  lGroupBalanceMask
  lGroupBalanceCpu
  lCpuSmtMask
  region
  linked =
  (a₁ : Addr) →
  (integer-memory : Addr → Int) →
  (pointer-memory : Addr → Addr) →
  (array : Addr) →
  (array-index : Int) →
  (source-memory : Addr → Int) →
  (i₈ i₃ i₉ : Int) →
  (other-source-memory : Addr → Int) →
  (i₅ i₆ : Int) →
  (allocation : Int → Int) →
  (i₁ i₂ i₄ i₇ i₁₀ : Int) →
  (allocation₄ allocation₁ allocation₂ allocation₃ : Int → Int) →
  let
    a₂ = shift a₁ threeZ
    x = integer-memory a₂
    a₃ = shift a₁ zeroZ
    a₄ = pointer-memory a₃
    a₅ = shift a₄ oneZ
    x₁ = integer-memory a₅
    a₆ = shift a₁ fourZ
    a₇ = pointer-memory a₆
    a₈ = shift a₇ zeroZ
    a₉ = pointer-memory a₈
    a₁₀ = shift a₁ oneZ
    x₂ = integer-memory a₁₀
    x₃ = integer-memory (shift a₉ x₂)
    a₁₁ = shift a₄ zeroZ
    a₁₂ = pointer-memory a₁₁
    a₁₃ = lGroupBalanceMask a₁₂
    a₁₄ = pointer-memory (shift a₁₃ zeroZ)
    a₁₅ = shift array array-index
    a₁₆ = shift a₁₅ zeroZ
    a₁₇ = pointer-memory a₁₆
    a₁₈ = shift a₁₇ zeroZ
    a₁₉ = shift a₉ zeroZ
    a₂₀ =
      havoc havoc-theory
        source-memory
        integer-memory
        a₁₈
        lSize
    a₂₁ = a₂₀ (shift a₁₇ i₈)
    a₂₂ = a₂₀ (shift a₉ i₃)
    a₂₃ = a₂₀ (shift a₉ i₈)
    a₂₄ = a₂₀ (shift a₁₄ i₃)
    a₂₅ = a₂₀ a₅
    a₂₆ = shift a₁₄ zeroZ
    a₂₇ = a₂₀ a₁₀
    lower-bound = toUint32 conversion i₉
    a₂₈ =
      havoc havoc-theory
        other-source-memory
        integer-memory
        a₁₈
        lSize
  in
  lIdleCpu i₅ ≠ zeroZ →
  lIdleCpu i₆ ≠ zeroZ →
  x ≠ twoZ →
  DivisibleByEight x₁ →
  integer-memory (shift a₉ i₅) ≠ zeroZ →
  integer-memory (shift a₉ i₆) ≠ zeroZ →
  x₃ ≠ zeroZ →
  integer-memory (shift a₁₄ i₅) ≠ zeroZ →
  integer-memory (shift a₁₄ i₆) ≠ zeroZ →
  zeroZ ≤Z array-index →
  array-index <Z lSize →
  zeroZ ≤Z i₅ →
  i₅ <Z lSize →
  zeroZ ≤Z i₆ →
  i₆ <Z lSize →
  zeroZ ≤Z i₉ →
  i₉ ≤Z lSize →
  zeroZ ≤Z x₂ →
  x₂ <Z lSize →
  region (base array) ≤Z zeroZ →
  region (base a₁) ≤Z zeroZ →
  Framed region pointer-memory →
  linked allocation →
  IsUint32 array-index →
  IsUint32 i₁ →
  IsSint32 i₂ →
  IsSint32 i₃ →
  IsSint32 i₄ →
  IsSint32 i₇ →
  IsSint32 i₈ →
  IsSint32 i₉ →
  IsSint32 i₁₀ →
  ValidRD allocation a₁ fiveZ →
  IsUint32 x →
  IsSint32 x₂ →
  ValidRD allocation a₆ oneZ →
  ValidRD allocation a₁₀ oneZ →
  ValidRD allocation a₂ oneZ →
  ValidRD allocation a₃ oneZ →
  ValidRD allocation a₁₅ oneZ →
  ValidRD allocation a₇ oneZ →
  ValidRD allocation (pointer-memory (shift a₁ twoZ)) twoZ →
  ValidRD allocation a₄ twoZ →
  IsSint32 x₁ →
  ValidRD allocation a₁₆ oneZ →
  ValidRD allocation a₈ oneZ →
  ValidRD allocation a₁₁ oneZ →
  ValidRD allocation a₁₂ oneZ →
  ValidRD allocation a₁₃ oneZ →
  IsUint8 x₃ →
  ValidRD allocation a₁₈ lSize →
  ValidRD allocation a₁₉ lSize →
  ValidRW allocation a₁₈ lSize →
  IsUint8 a₂₁ →
  IsUint8 a₂₂ →
  IsUint8 a₂₃ →
  IsUint8 a₂₄ →
  IsSint32 a₂₅ →
  ValidRD allocation a₂₆ lSize →
  Separated a₁₈ lSize a₂₆ lSize →
  Conditional
    (toUint32 conversion i₈ <Z lSize)
    (ThenState
      havoc-theory
      lSize
      lIdleCpu
      lSchedGroupCpus
      lSchedGroupMask
      lGroupBalanceMask
      lCpuSmtMask
      array
      a₃
      a₅
      a₁₀
      a₁₈
      source-memory
      integer-memory
      pointer-memory
      allocation
      allocation₄
      i₁
      i₂
      i₈
      i₁₀
      a₂₇
      a₂₅)
    (ElseState
      lGroupBalanceCpu
      a₁₂
      a₂₇
      allocation
      allocation₁
      allocation₂
      allocation₃
      i₂
      i₃
      i₄
      i₇
      a₁₀) →
  (LandSevenNonzero a₂₅ → i₃ ≡ minusOneZ) →
  (i₃ ≠ minusOneZ →
    lIdleCpu i₃ ≠ zeroZ ∧
    a₂₂ ≠ zeroZ ∧
    a₂₄ ≠ zeroZ ∧
    zeroZ ≤Z i₃ ∧
    i₃ <Z lSize) →
  (i₃ ≡ minusOneZ →
    ((index : Int) →
      a₂₀ (shift a₁₄ index) ≠ zeroZ →
      zeroZ ≤Z index →
      index <Z lSize →
      a₂₀ (shift a₁₇ index) ≠ zeroZ)) →
  (HasActiveFrom a₂₀ a₁₇ a₉ lower-bound lSize →
    i₈ <Z lSize) →
  (HasActiveFrom a₂₀ a₁₇ a₉ lower-bound lSize →
    i₈ <Z lSize ∧
    lower-bound ≤Z i₈) →
  (HasActiveFrom a₂₀ a₁₇ a₉ lower-bound lSize →
    a₂₁ ≠ zeroZ ∧
    a₂₃ ≠ zeroZ) →
  (((index : Int) →
      index <Z lSize →
      lower-bound ≤Z index →
      Either
        (a₂₀ (shift a₁₇ index) ≡ zeroZ)
        (a₂₀ (shift a₉ index) ≡ zeroZ)) →
    lSize ≡ i₈) →
  (i₃ ≠ minusOneZ →
    ((index : Int) →
      a₂₀ (shift a₉ index) ≠ zeroZ →
      a₂₀ (shift a₁₄ index) ≠ zeroZ →
      zeroZ ≤Z index →
      index <Z i₃ →
      index <Z lSize →
      lIdleCpu index ≡ zeroZ)) →
  (i₃ ≡ minusOneZ →
    ((index : Int) →
      a₂₀ (shift a₉ index) ≠ zeroZ →
      a₂₀ (shift a₁₄ index) ≠ zeroZ →
      zeroZ ≤Z index →
      index <Z i₉ →
      index <Z lSize →
      lIdleCpu index ≡ zeroZ)) →
  (HasActiveFrom a₂₀ a₁₇ a₉ lower-bound lSize →
    ((index : Int) →
      index <Z i₈ →
      lower-bound ≤Z index →
      Either
        (a₂₀ (shift a₁₇ index) ≡ zeroZ)
        (a₂₀ (shift a₉ index) ≡ zeroZ))) →
  (i₃ ≠ minusOneZ →
    ((index : Int) →
      a₂₀ (shift a₉ index) ≠ zeroZ →
      a₂₀ (shift a₁₄ index) ≠ zeroZ →
      zeroZ ≤Z index →
      i₃ ≤Z index →
      index <Z i₉ →
      index <Z lSize →
      Not
        (IdleCore
          lSize
          lIdleCpu
          lCpuSmtMask
          pointer-memory
          a₂₀
          index))) →
  (i₃ ≠ minusOneZ →
    ((index : Int) →
      a₂₀ (shift a₁₄ index) ≠ zeroZ →
      zeroZ ≤Z index →
      index <Z lSize →
      Either
        (a₂₀ (shift a₁₇ index) ≠ zeroZ)
        (Not
          (IdleCore
            lSize
            lIdleCpu
            lCpuSmtMask
            pointer-memory
            a₂₀
            index)))) →
  ((index : Int) →
    zeroZ ≤Z index →
    index <Z lSize →
    Separated
      a₁₉
      lSize
      (shift
        (pointer-memory (shift (shift array index) zeroZ))
        zeroZ)
      lSize) →
  ArrayStorageInvariant
    allocation
    pointer-memory
    array
    lSize
    lSize →
  ((index : Int) →
    zeroZ ≤Z index →
    index <Z lSize →
    ((a₂₈ (shift a₁₄ index) ≠ zeroZ) ↔
      (a₂₈ (shift a₁₇ index) ≠ zeroZ))) →
  ((index : Int) →
    a₂₀ (shift a₁₇ index) ≠ zeroZ →
    zeroZ ≤Z index →
    index <Z lSize →
    a₂₀ (shift a₁₄ index) ≠ zeroZ) →
  ((index : Int) →
    integer-memory (shift a₉ index) ≠ zeroZ →
    integer-memory (shift a₁₄ index) ≠ zeroZ →
    zeroZ ≤Z index →
    index <Z lSize →
    Not
      (IdleCore
        lSize
        lIdleCpu
        lCpuSmtMask
        pointer-memory
        integer-memory
        index)) →
  ((index : Int) →
    integer-memory (shift a₉ index) ≠ zeroZ →
    integer-memory (shift a₁₄ index) ≠ zeroZ →
    zeroZ ≤Z index →
    index <Z i₆ →
    index <Z lSize →
    lIdleCpu index ≡ zeroZ) →
  MaskStorageInvariant
    allocation pointer-memory array lSize lSchedGroupCpus →
  MaskStorageInvariant
    allocation pointer-memory array lSize lSchedGroupMask →
  MaskStorageInvariant
    allocation pointer-memory array lSize lGroupBalanceMask →
  CpuSmtStorageInvariant
    allocation pointer-memory array lSize lCpuSmtMask →
  (x₂ ≡ i₆) ↔ (i₂ ≠ zeroZ)

should-we-balance-not-newly-idle-with-idle-cpu-post-2-goal39 : Set₁
should-we-balance-not-newly-idle-with-idle-cpu-post-2-goal39 =
  (conversion : Uint32Projection) →
  (havoc-theory : HavocTheory) →
  (lSize : Int) →
  ((zeroZ <Z lSize) ∧ (lSize ≤Z signed32Maximum)) →
  (lIdleCpu : Int → Int) →
  (lSchedGroupCpus : Addr → Addr) →
  (lSchedGroupMask : Addr → Addr) →
  (lGroupBalanceMask : Addr → Addr) →
  (lGroupBalanceCpu : Addr → Int) →
  (lCpuSmtMask : Int → Addr) →
  (cpu-mask-theory : CpuMaskTheory lSize lIdleCpu lCpuSmtMask) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  Goal39
    conversion
    havoc-theory
    lSize
    lIdleCpu
    lSchedGroupCpus
    lSchedGroupMask
    lGroupBalanceMask
    lGroupBalanceCpu
    lCpuSmtMask
    region
    linked
