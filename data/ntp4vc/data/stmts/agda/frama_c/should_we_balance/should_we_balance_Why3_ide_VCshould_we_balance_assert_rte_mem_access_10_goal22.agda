-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_assert_rte_mem_access_10_goal22:
-- under the stated integer-range, memory-validity, separation, framing,
-- linkedness, mask, havoc-update, and loop-state assumptions, the address
-- computed from a at index i is readable for one byte. This file contains no proof.

{-# OPTIONS --safe #-}

module should-we-balance-Why3-ide-VCshould-we-balance-assert-rte-mem-access-10-goal22 where

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

Goal22 :
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
Goal22
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
  (integer-memory₁ integer-memory₂ : Addr → Int) →
  (i₁ i₂ : Int) →
  (allocation : Int → Int) →
  let
    a₂ = shift a₁ threeZ
    x = integer-memory a₂
    a₃ = shift a₁ fourZ
    a₄ = pointer-memory a₃
    a₅ = pointer-memory (shift a₄ zeroZ)
    a₆ = shift a₁ oneZ
    x₁ = integer-memory a₆
    x₂ = integer-memory (shift a₅ x₁)
    a₇ = shift a₁ zeroZ
    a₈ = shift a i
    a₉ = pointer-memory a₇
    a₁₀ = shift a₉ oneZ
    a₁₁ = shift a₉ zeroZ
    a₁₂ = pointer-memory a₁₁
    a₁₃ = lGroupBalanceMask a₁₂
    a₁₄ = shift a₅ zeroZ
    a₁₅ = shift a₈ zeroZ
    a₁₆ = pointer-memory a₁₅
    a₁₇ = shift a₁₆ zeroZ
    a₁₈ =
      havoc havoc-theory
        integer-memory₁
        integer-memory
        a₁₇
        lSize
    a₁₉ = pointer-memory (shift a₁₃ zeroZ)
    a₂₀ =
      havoc havoc-theory
        integer-memory₂
        integer-memory
        a₁₇
        lSize
    a₂₁ = a₂₀ (shift a₅ i₁)
    a₂₂ = a₂₀ (shift a₁₉ i₁)
    a₂₃ = a₂₀ a₁₀
    a₂₄ = shift a₁₉ zeroZ
  in
  x ≠ twoZ →
  x₂ ≠ zeroZ →
  zeroZ ≤Z i →
  i <Z lSize →
  zeroZ ≤Z i₂ →
  i₂ ≤Z lSize →
  zeroZ ≤Z x₁ →
  x₁ <Z lSize →
  region (base a) ≤Z zeroZ →
  region (base a₁) ≤Z zeroZ →
  Framed region pointer-memory →
  linked allocation →
  IsUint32 i →
  IsSint32 i₁ →
  IsSint32 i₂ →
  ValidRD allocation a₁ fiveZ →
  IsUint32 x →
  IsSint32 x₁ →
  ValidRD allocation a₃ oneZ →
  ValidRD allocation a₆ oneZ →
  ValidRD allocation a₂ oneZ →
  ValidRD allocation a₇ oneZ →
  ValidRD allocation a₈ oneZ →
  ValidRD allocation a₄ oneZ →
  ValidRD allocation (pointer-memory (shift a₁ twoZ)) twoZ →
  ValidRD allocation a₉ twoZ →
  IsSint32 (integer-memory a₁₀) →
  ValidRD allocation a₁₁ oneZ →
  ValidRD allocation a₁₂ oneZ →
  ValidRD allocation a₁₃ oneZ →
  IsUint8 x₂ →
  ValidRD allocation a₁₄ lSize →
  ValidRW allocation a₁₇ lSize →
  IsUint8 (a₁₈ (shift a₅ minusOneZ)) →
  IsUint8 (a₁₈ (shift a₁₉ minusOneZ)) →
  IsUint8 a₂₁ →
  IsUint8 a₂₂ →
  IsSint32 (a₁₈ a₁₀) →
  IsSint32 a₂₃ →
  ValidRD allocation a₂₄ lSize →
  Separated a₁₇ lSize a₂₄ lSize →
  (LandSevenNonzero a₂₃ → i₁ ≡ minusOneZ) →
  (i₁ ≠ minusOneZ →
    lIdleCpu i₁ ≠ zeroZ ∧
    a₂₁ ≠ zeroZ ∧
    a₂₂ ≠ zeroZ ∧
    zeroZ ≤Z i₁ ∧
    i₁ <Z lSize) →
  (i₁ ≡ minusOneZ →
    ((index : Int) →
      a₂₀ (shift a₁₉ index) ≠ zeroZ →
      zeroZ ≤Z index →
      index <Z lSize →
      a₂₀ (shift a₁₆ index) ≠ zeroZ)) →
  (i₁ ≠ minusOneZ →
    ((index : Int) →
      a₂₀ (shift a₅ index) ≠ zeroZ →
      a₂₀ (shift a₁₉ index) ≠ zeroZ →
      zeroZ ≤Z index →
      index <Z i₁ →
      index <Z lSize →
      lIdleCpu index ≡ zeroZ)) →
  (i₁ ≡ minusOneZ →
    ((index : Int) →
      a₂₀ (shift a₅ index) ≠ zeroZ →
      a₂₀ (shift a₁₉ index) ≠ zeroZ →
      zeroZ ≤Z index →
      index <Z i₂ →
      index <Z lSize →
      lIdleCpu index ≡ zeroZ)) →
  (i₁ ≠ minusOneZ →
    ((index : Int) →
      a₂₀ (shift a₅ index) ≠ zeroZ →
      a₂₀ (shift a₁₉ index) ≠ zeroZ →
      zeroZ ≤Z index →
      i₁ ≤Z index →
      index <Z i₂ →
      index <Z lSize →
      Not
        (IdleCore
          lSize
          lIdleCpu
          lCpuSmtMask
          pointer-memory
          a₂₀
          index))) →
  (i₁ ≠ minusOneZ →
    ((index : Int) →
      a₂₀ (shift a₁₉ index) ≠ zeroZ →
      zeroZ ≤Z index →
      index <Z lSize →
      Either
        (a₂₀ (shift a₁₆ index) ≠ zeroZ)
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
      a₁₄
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
    ((a₁₈ (shift a₁₉ index) ≠ zeroZ) ↔
      (a₁₈ (shift a₁₆ index) ≠ zeroZ))) →
  ((index : Int) →
    a₂₀ (shift a₁₆ index) ≠ zeroZ →
    zeroZ ≤Z index →
    index <Z lSize →
    a₂₀ (shift a₁₉ index) ≠ zeroZ) →
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
  ValidRD allocation a₁₅ oneZ

should-we-balance-assert-rte-mem-access-10-goal22 : Set₁
should-we-balance-assert-rte-mem-access-10-goal22 =
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
  Goal22
    havoc-theory
    lSize
    lIdleCpu
    lSchedGroupCpus
    lSchedGroupMask
    lGroupBalanceMask
    lCpuSmtMask
    region
    linked
