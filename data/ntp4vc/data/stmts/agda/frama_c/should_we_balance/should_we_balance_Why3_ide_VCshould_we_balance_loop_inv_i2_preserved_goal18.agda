-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_loop_inv_i2_preserved_goal18:
-- under the stated integer-range, memory-validity, separation, framing,
-- linkedness, havoc-update, CPU-mask, and loop-invariant assumptions, the
-- idle-CPU flag at index i_1 is zero. This file contains no proof.

{-# OPTIONS --safe #-}

module should-we-balance-Why3-ide-VCshould-we-balance-loop-inv-i2-preserved-goal18 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

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

minusOneZ zeroZ oneZ twoZ threeZ fourZ fiveZ : Int
minusOneZ = negsuc zero
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos 2
threeZ = pos 3
fourZ = pos 4
fiveZ = pos 5

uint8Upper uint32Upper : Int
uint8Upper = pos 256
uint32Upper = pos 4294967296

signed32Lower signed32Upper signed32Maximum signed32MaximumMinusOne : Int
signed32Lower = negsuc 2147483647
signed32Upper = pos 2147483648
signed32Maximum = pos 2147483647
signed32MaximumMinusOne = pos 2147483646

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

-- Imported A_schedule_cpumask laws are explicit assumptions, not postulates.
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

HasCommonActiveFrom :
  (Addr → Int) →
  Addr →
  Addr →
  Int →
  Int →
  Set
HasCommonActiveFrom integer-memory first-mask second-mask lower upper =
  Exists Int λ index →
    integer-memory (shift first-mask index) ≠ zeroZ ∧
    integer-memory (shift second-mask index) ≠ zeroZ ∧
    index <Z upper ∧
    lower ≤Z index

MaskStorageAssumption :
  Int →
  (Addr → Addr) →
  Addr →
  (Int → Int) →
  (Addr → Addr) →
  Set
MaskStorageAssumption lSize pointer-memory a allocation mask-field =
  (address : Addr) →
  let
    mask = mask-field address
    contents =
      shift
        (pointer-memory (shift mask zeroZ))
        zeroZ
  in
  ValidRD allocation mask oneZ ∧
  ValidRD allocation contents lSize ∧
  ((index : Int) →
    zeroZ ≤Z index →
    index <Z lSize →
    Separated
      contents
      lSize
      (shift
        (pointer-memory (shift (shift a index) zeroZ))
        zeroZ)
      lSize)

Goal18 :
  Uint32Projection →
  HavocTheory →
  Int →
  (Int → Int) →
  (Addr → Addr) →
  (Addr → Addr) →
  (Addr → Addr) →
  (Int → Addr) →
  (Int → Int) →
  ((Int → Int) → Set) →
  Set
Goal18
  conversion
  havoc-theory
  lSize
  lIdleCpu
  lSchedGroupCpus
  lSchedGroupMask
  lGroupBalanceMask
  lCpuSmtMask
  region
  linked =
  (a₁ : Addr) →
  (integer-memory : Addr → Int) →
  (pointer-memory : Addr → Addr) →
  (a : Addr) →
  (i : Int) →
  (integer-memory₂ : Addr → Int) →
  (integer-memory₁ : Addr → Int) →
  (i₂ i₃ i₁ : Int) →
  (allocation : Int → Int) →
  let
    a₂ = shift a₁ threeZ
    x = integer-memory a₂
    a₃ = shift a₁ fourZ
    a₄ = pointer-memory a₃
    a₅ = shift a₄ zeroZ
    a₆ = pointer-memory a₅
    a₇ = shift a₁ oneZ
    x₁ = integer-memory a₇
    x₂ = integer-memory (shift a₆ x₁)
    a₈ = shift a i
    a₉ = shift a₈ zeroZ
    a₁₀ = pointer-memory a₉
    a₁₁ = shift a₁₀ zeroZ
    a₁₂ =
      havoc havoc-theory
        integer-memory₂
        integer-memory
        a₁₁
        lSize
    a₁₃ = shift a₁ zeroZ
    a₁₄ = pointer-memory a₁₃
    a₁₅ = shift a₁₄ zeroZ
    a₁₆ = pointer-memory a₁₅
    a₁₇ = lGroupBalanceMask a₁₆
    a₁₈ = pointer-memory (shift a₁₇ zeroZ)
    a₁₉ = shift a₁₄ oneZ
    a₂₀ = shift a₆ zeroZ
    a₂₁ =
      havoc havoc-theory
        integer-memory₁
        integer-memory
        a₁₁
        lSize
    a₂₂ = shift a₆ minusOneZ
    a₂₃ = shift a₁₈ minusOneZ
    a₂₄ = a₁₂ (shift a₁₀ i₂)
    a₂₅ = a₁₂ (shift a₆ i₂)
    a₂₆ = shift a₁₈ zeroZ
    x₃ = toUint32 conversion i₃
  in
  lIdleCpu i₂ ≡ zeroZ →
  x ≠ twoZ →
  x₂ ≠ zeroZ →
  a₁₂ (shift a₆ i₁) ≠ zeroZ →
  a₁₂ (shift a₁₈ i₁) ≠ zeroZ →
  zeroZ ≤Z i →
  i <Z lSize →
  zeroZ ≤Z i₁ →
  i₁ <Z lSize →
  zeroZ ≤Z i₂ →
  i₁ ≤Z i₂ →
  i₂ <Z lSize →
  zeroZ ≤Z i₃ →
  i₃ ≤Z lSize →
  toUint32 conversion i₂ <Z lSize →
  zeroZ ≤Z x₁ →
  x₁ <Z lSize →
  region (base a) ≤Z zeroZ →
  region (base a₁) ≤Z zeroZ →
  i₂ ≤Z signed32MaximumMinusOne →
  Framed region pointer-memory →
  linked allocation →
  IsUint32 i →
  IsSint32 i₂ →
  IsSint32 i₃ →
  ValidRD allocation a₁ fiveZ →
  IsUint32 x →
  IsSint32 (addInt oneZ i₂) →
  IsSint32 x₁ →
  ValidRD allocation a₃ oneZ →
  ValidRD allocation a₇ oneZ →
  ValidRD allocation a₂ oneZ →
  ValidRD allocation a₁₃ oneZ →
  ValidRD allocation a₈ oneZ →
  ValidRD allocation a₄ oneZ →
  ValidRD
    allocation
    (pointer-memory (shift a₁ twoZ))
    twoZ →
  ValidRD allocation a₁₄ twoZ →
  IsSint32 (integer-memory a₁₉) →
  ValidRD allocation a₉ oneZ →
  ValidRD allocation a₅ oneZ →
  ValidRD allocation a₁₅ oneZ →
  ValidRD allocation a₁₆ oneZ →
  ValidRD allocation a₁₇ oneZ →
  IsUint8 x₂ →
  ValidRD allocation a₁₁ lSize →
  ValidRD allocation a₂₀ lSize →
  ValidRW allocation a₁₁ lSize →
  IsUint8 (a₂₁ a₂₂) →
  IsUint8 (a₂₁ a₂₃) →
  IsUint8 a₂₄ →
  IsUint8 (a₁₂ a₂₂) →
  IsUint8 a₂₅ →
  IsUint8 (a₁₂ a₂₃) →
  IsSint32 (a₂₁ a₁₉) →
  IsSint32 (a₁₂ a₁₉) →
  ValidRD allocation a₂₆ lSize →
  Separated a₁₁ lSize a₂₆ lSize →
  (HasCommonActiveFrom a₁₂ a₁₀ a₆ x₃ lSize →
    x₃ ≤Z i₂) →
  (HasCommonActiveFrom a₁₂ a₁₀ a₆ x₃ lSize →
    (a₂₄ ≠ zeroZ) ∧ (a₂₅ ≠ zeroZ)) →
  (((index : Int) →
      index <Z lSize →
      x₃ ≤Z index →
      Either
        (a₁₂ (shift a₁₀ index) ≡ zeroZ)
        (a₁₂ (shift a₆ index) ≡ zeroZ)) →
    lSize ≡ i₂) →
  (HasCommonActiveFrom a₁₂ a₁₀ a₆ x₃ lSize →
    ((index : Int) →
      index <Z i₂ →
      x₃ ≤Z index →
      Either
        (a₁₂ (shift a₁₀ index) ≡ zeroZ)
        (a₁₂ (shift a₆ index) ≡ zeroZ))) →
  ((index : Int) →
    zeroZ ≤Z index →
    index <Z lSize →
    Separated
      a₂₀
      lSize
      (shift
        (pointer-memory (shift (shift a index) zeroZ))
        zeroZ)
      lSize) →
  ((index : Int) →
    let current = shift a index
    in
    zeroZ ≤Z index →
    index <Z lSize →
    ValidRD allocation current oneZ ∧
    ValidRW
      allocation
      (shift
        (pointer-memory (shift current zeroZ))
        zeroZ)
      lSize) →
  ((index : Int) →
    zeroZ ≤Z index →
    index <Z lSize →
    ((a₂₁ (shift a₁₈ index) ≠ zeroZ) ↔
      (a₂₁ (shift a₁₀ index) ≠ zeroZ))) →
  ((index : Int) →
    a₁₂ (shift a₁₈ index) ≠ zeroZ →
    zeroZ ≤Z index →
    index <Z lSize →
    a₁₂ (shift a₁₀ index) ≠ zeroZ) →
  ((index : Int) →
    a₁₂ (shift a₁₀ index) ≠ zeroZ →
    zeroZ ≤Z index →
    index <Z lSize →
    a₁₂ (shift a₁₈ index) ≠ zeroZ) →
  ((index : Int) →
    a₁₂ (shift a₆ index) ≠ zeroZ →
    a₁₂ (shift a₁₈ index) ≠ zeroZ →
    zeroZ ≤Z index →
    index <Z i₃ →
    index <Z lSize →
    lIdleCpu index ≡ zeroZ) →
  MaskStorageAssumption
    lSize
    pointer-memory
    a
    allocation
    lSchedGroupCpus →
  MaskStorageAssumption
    lSize
    pointer-memory
    a
    allocation
    lSchedGroupMask →
  MaskStorageAssumption
    lSize
    pointer-memory
    a
    allocation
    lGroupBalanceMask →
  ((index : Int) →
    let
      mask = lCpuSmtMask index
      contents =
        shift
          (pointer-memory (shift mask zeroZ))
          zeroZ
    in
    zeroZ ≤Z index →
    index <Z lSize →
    ValidRD allocation mask oneZ ∧
    ValidRD allocation contents lSize ∧
    ((other-index : Int) →
      zeroZ ≤Z other-index →
      other-index <Z lSize →
      Separated
        contents
        lSize
        (shift
          (pointer-memory (shift (shift a other-index) zeroZ))
          zeroZ)
        lSize)) →
  lIdleCpu i₁ ≡ zeroZ

should-we-balance-loop-invariant-i2-preserved-goal18 : Set₁
should-we-balance-loop-invariant-i2-preserved-goal18 =
  (conversion : Uint32Projection) →
  (havoc-theory : HavocTheory) →
  (lSize : Int) →
  ((zeroZ <Z lSize) ∧ (lSize ≤Z signed32Maximum)) →
  (lIdleCpu : Int → Int) →
  (lSchedGroupCpus : Addr → Addr) →
  (lSchedGroupMask : Addr → Addr) →
  (lGroupBalanceMask : Addr → Addr) →
  (lCpuSmtMask : Int → Addr) →
  (cpu-mask-theory : CpuMaskTheory lSize lIdleCpu lCpuSmtMask) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  Goal18
    conversion
    havoc-theory
    lSize
    lIdleCpu
    lSchedGroupCpus
    lSchedGroupMask
    lGroupBalanceMask
    lCpuSmtMask
    region
    linked
