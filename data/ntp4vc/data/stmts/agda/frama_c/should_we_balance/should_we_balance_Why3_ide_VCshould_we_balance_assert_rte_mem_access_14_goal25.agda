-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_assert_rte_mem_access_14_goal25:
-- under the stated integer-range, memory-validity, separation, framing,
-- linkedness, CPU-mask theory, havoc-update, and loop-state assumptions, the
-- address at offset one from the dereferenced base pointer is readable for one
-- byte. This file contains no proof.

{-# OPTIONS --safe #-}

module should-we-balance-Why3-ide-VCshould-we-balance-assert-rte-mem-access-14-goal25 where

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

zeroZ oneZ twoZ threeZ fourZ fiveZ sevenZ eightZ minusOneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos 2
threeZ = pos 3
fourZ = pos 4
fiveZ = pos 5
sevenZ = pos 7
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

Goal25 :
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
Goal25
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
  (i₁ : Int) →
  (integer-memory₁ integer-memory₂ : Addr → Int) →
  (i₃ i₂ i₄ : Int) →
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
    a₈ = shift a₁ zeroZ
    a₉ = shift a i₁
    a₁₀ = pointer-memory a₈
    a₁₁ = shift a₁₀ oneZ
    a₁₂ = shift a₉ zeroZ
    a₁₃ = shift a₁₀ zeroZ
    a₁₄ = pointer-memory a₁₃
    a₁₅ = lGroupBalanceMask a₁₄
    a₁₆ = pointer-memory a₁₂
    a₁₇ = shift a₁₆ zeroZ
    a₁₈ = shift a₆ zeroZ
    a₁₉ =
      havoc havoc-theory
        integer-memory₁
        integer-memory
        a₁₇
        lSize
    a₂₀ = pointer-memory (shift a₁₅ zeroZ)
    a₂₁ =
      havoc havoc-theory
        integer-memory₂
        integer-memory
        a₁₇
        lSize
    a₂₂ = a₂₁ (shift a₁₆ i₃)
    a₂₃ = a₂₁ (shift a₆ i₂)
    a₂₄ = a₂₁ (shift a₆ i₃)
    a₂₅ = a₂₁ (shift a₂₀ i₂)
    a₂₆ = a₂₁ a₁₁
    a₂₇ = shift a₂₀ zeroZ
    x₃ = toUint32 conversion i₄
  in
  lIdleCpu i₃ ≠ zeroZ →
  x ≠ twoZ →
  x₂ ≠ zeroZ →
  zeroZ ≤Z i₁ →
  i₁ <Z lSize →
  zeroZ ≤Z i₃ →
  i₃ <Z lSize →
  zeroZ ≤Z i₄ →
  i₄ ≤Z lSize →
  toUint32 conversion i₃ <Z lSize →
  zeroZ ≤Z x₁ →
  x₁ <Z lSize →
  region (base a) ≤Z zeroZ →
  region (base a₁) ≤Z zeroZ →
  Framed region pointer-memory →
  linked allocation →
  IsUint32 i₁ →
  IsSint32 i₂ →
  IsSint32 i₃ →
  IsSint32 i₄ →
  ValidRD allocation a₁ fiveZ →
  IsUint32 x →
  IsSint32 x₁ →
  ValidRD allocation a₃ oneZ →
  ValidRD allocation a₇ oneZ →
  ValidRD allocation a₂ oneZ →
  ValidRD allocation a₈ oneZ →
  ValidRD allocation a₉ oneZ →
  ValidRD allocation a₄ oneZ →
  ValidRD allocation (pointer-memory (shift a₁ twoZ)) twoZ →
  ValidRD allocation a₁₀ twoZ →
  IsSint32 (integer-memory a₁₁) →
  ValidRD allocation a₁₂ oneZ →
  ValidRD allocation a₅ oneZ →
  ValidRD allocation a₁₃ oneZ →
  ValidRD allocation a₁₄ oneZ →
  ValidRD allocation a₁₅ oneZ →
  IsUint8 x₂ →
  ValidRD allocation a₁₇ lSize →
  ValidRD allocation a₁₈ lSize →
  ValidRW allocation a₁₇ lSize →
  IsUint8 (a₁₉ (shift a₆ minusOneZ)) →
  IsUint8 (a₁₉ (shift a₂₀ minusOneZ)) →
  IsUint8 a₂₂ →
  IsUint8 a₂₃ →
  IsUint8 a₂₄ →
  IsUint8 a₂₅ →
  IsSint32 (a₁₉ a₁₁) →
  IsSint32 a₂₆ →
  ValidRD allocation a₂₇ lSize →
  Separated a₁₇ lSize a₂₇ lSize →
  (LandSevenNonzero a₂₆ → i₂ ≡ minusOneZ) →
  (i₂ ≠ minusOneZ →
    lIdleCpu i₂ ≠ zeroZ ∧
    a₂₃ ≠ zeroZ ∧
    a₂₅ ≠ zeroZ ∧
    zeroZ ≤Z i₂ ∧
    i₂ <Z lSize) →
  (i₂ ≡ minusOneZ →
    ((index : Int) →
      a₂₁ (shift a₂₀ index) ≠ zeroZ →
      zeroZ ≤Z index →
      index <Z lSize →
      a₂₁ (shift a₁₆ index) ≠ zeroZ)) →
  (HasActiveFrom a₂₁ a₁₆ a₆ x₃ lSize →
    x₃ ≤Z i₃) →
  (HasActiveFrom a₂₁ a₁₆ a₆ x₃ lSize →
    a₂₂ ≠ zeroZ ∧
    a₂₄ ≠ zeroZ) →
  (((index : Int) →
      index <Z lSize →
      x₃ ≤Z index →
      Either
        (a₂₁ (shift a₁₆ index) ≡ zeroZ)
        (a₂₁ (shift a₆ index) ≡ zeroZ)) →
    lSize ≡ i₃) →
  (i₂ ≠ minusOneZ →
    ((index : Int) →
      a₂₁ (shift a₆ index) ≠ zeroZ →
      a₂₁ (shift a₂₀ index) ≠ zeroZ →
      zeroZ ≤Z index →
      index <Z i₂ →
      index <Z lSize →
      lIdleCpu index ≡ zeroZ)) →
  (i₂ ≡ minusOneZ →
    ((index : Int) →
      a₂₁ (shift a₆ index) ≠ zeroZ →
      a₂₁ (shift a₂₀ index) ≠ zeroZ →
      zeroZ ≤Z index →
      index <Z i₄ →
      index <Z lSize →
      lIdleCpu index ≡ zeroZ)) →
  (HasActiveFrom a₂₁ a₁₆ a₆ x₃ lSize →
    ((index : Int) →
      index <Z i₃ →
      x₃ ≤Z index →
      Either
        (a₂₁ (shift a₁₆ index) ≡ zeroZ)
        (a₂₁ (shift a₆ index) ≡ zeroZ))) →
  (i₂ ≠ minusOneZ →
    ((index : Int) →
      a₂₁ (shift a₆ index) ≠ zeroZ →
      a₂₁ (shift a₂₀ index) ≠ zeroZ →
      zeroZ ≤Z index →
      i₂ ≤Z index →
      index <Z i₄ →
      index <Z lSize →
      Not
        (IdleCore
          lSize
          lIdleCpu
          lCpuSmtMask
          pointer-memory
          a₂₁
          index))) →
  (i₂ ≠ minusOneZ →
    ((index : Int) →
      a₂₁ (shift a₂₀ index) ≠ zeroZ →
      zeroZ ≤Z index →
      index <Z lSize →
      Either
        (a₂₁ (shift a₁₆ index) ≠ zeroZ)
        (Not
          (IdleCore
            lSize
            lIdleCpu
            lCpuSmtMask
            pointer-memory
            a₂₁
            index)))) →
  ((index : Int) →
    zeroZ ≤Z index →
    index <Z lSize →
    Separated
      a₁₈
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
    ((a₁₉ (shift a₂₀ index) ≠ zeroZ) ↔
      (a₁₉ (shift a₁₆ index) ≠ zeroZ))) →
  ((index : Int) →
    a₂₁ (shift a₁₆ index) ≠ zeroZ →
    zeroZ ≤Z index →
    index <Z lSize →
    a₂₁ (shift a₂₀ index) ≠ zeroZ) →
  ((address : Addr) →
    let
      mask = lSchedGroupCpus address
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
        lSize)) →
  ((address : Addr) →
    let
      mask = lSchedGroupMask address
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
        lSize)) →
  ((address : Addr) →
    let
      mask = lGroupBalanceMask address
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
        lSize)) →
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
  ValidRD allocation a₁₁ oneZ

should-we-balance-assert-rte-mem-access-14-goal25 : Set₁
should-we-balance-assert-rte-mem-access-14-goal25 =
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
  Goal25
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
