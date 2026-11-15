-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/should_we_balance/is_core_idle_Why3_ide_VCis_core_idle_call_find_next_bit_pre_2_goal8:
-- under the stated integer bounds, memory-validity, separation, framing,
-- linkedness, and idle-CPU assumptions, the CPU SMT-mask range is readable.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module is-core-idle-Why3-ide-VCis-core-idle-call-find-next-bit-pre-2-goal8 where

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

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

uint8Upper uint32Upper signed32Lower signed32Upper signed32Maximum : Int
uint8Upper = pos 256
uint32Upper = pos 4294967296
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

Goal8 :
  Int →
  (Int → Int) →
  (Addr → Addr) →
  (Addr → Addr) →
  (Addr → Addr) →
  (Int → Addr) →
  (Int → Int) →
  ((Int → Int) → Set) →
  Set
Goal8
  lSize
  lIdleCpu
  lSchedGroupCpus
  lSchedGroupMask
  lGroupBalanceMask
  lCpuSmtMask
  region
  linked =
  (i₂ : Int) →
  (pointer-memory : Addr → Addr) →
  (i i₁ : Int) →
  (a : Addr) →
  (allocation : Int → Int) →
  (integer-memory : Addr → Int) →
  let
    a₁ = shift (lCpuSmtMask i₂) zeroZ
    a₂ = pointer-memory a₁
  in
  lIdleCpu i₂ ≠ zeroZ →
  zeroZ ≤Z i →
  i <Z lSize →
  zeroZ ≤Z i₁ →
  zeroZ ≤Z i₂ →
  i₂ <Z lSize →
  i₁ ≤Z lSize →
  region (base a) ≤Z zeroZ →
  Framed region pointer-memory →
  linked allocation →
  IsUint32 i →
  IsSint32 i₁ →
  IsSint32 i₂ →
  ValidRD allocation a₁ oneZ →
  ((i₃ : Int) →
    integer-memory (shift a₂ i₃) ≠ zeroZ →
    zeroZ ≤Z i₃ →
    i₃ <Z i₁ →
    lIdleCpu i₃ ≠ zeroZ) →
  ((i₃ : Int) →
    let a₃ = shift a i₃
    in
    zeroZ ≤Z i₃ →
    i₃ <Z lSize →
    ValidRD allocation a₃ oneZ ∧
    ValidRW
      allocation
      (shift (pointer-memory (shift a₃ zeroZ)) zeroZ)
      lSize) →
  ((a₃ : Addr) →
    let
      a₄ = lSchedGroupCpus a₃
      a₅ = shift (pointer-memory (shift a₄ zeroZ)) zeroZ
    in
    ValidRD allocation a₄ oneZ ∧
    ValidRD allocation a₅ lSize ∧
    ((i₃ : Int) →
      zeroZ ≤Z i₃ →
      i₃ <Z lSize →
      Separated
        a₅
        lSize
        (shift
          (pointer-memory (shift (shift a i₃) zeroZ))
          zeroZ)
        lSize)) →
  ((a₃ : Addr) →
    let
      a₄ = lSchedGroupMask a₃
      a₅ = shift (pointer-memory (shift a₄ zeroZ)) zeroZ
    in
    ValidRD allocation a₄ oneZ ∧
    ValidRD allocation a₅ lSize ∧
    ((i₃ : Int) →
      zeroZ ≤Z i₃ →
      i₃ <Z lSize →
      Separated
        a₅
        lSize
        (shift
          (pointer-memory (shift (shift a i₃) zeroZ))
          zeroZ)
        lSize)) →
  ((a₃ : Addr) →
    let
      a₄ = lGroupBalanceMask a₃
      a₅ = shift (pointer-memory (shift a₄ zeroZ)) zeroZ
    in
    ValidRD allocation a₄ oneZ ∧
    ValidRD allocation a₅ lSize ∧
    ((i₃ : Int) →
      zeroZ ≤Z i₃ →
      i₃ <Z lSize →
      Separated
        a₅
        lSize
        (shift
          (pointer-memory (shift (shift a i₃) zeroZ))
          zeroZ)
        lSize)) →
  ((i₃ : Int) →
    let
      a₃ = lCpuSmtMask i₃
      a₄ = shift (pointer-memory (shift a₃ zeroZ)) zeroZ
    in
    zeroZ ≤Z i₃ →
    i₃ <Z lSize →
    ValidRD allocation a₃ oneZ ∧
    ValidRD allocation a₄ lSize ∧
    ((i₄ : Int) →
      zeroZ ≤Z i₄ →
      i₄ <Z lSize →
      Separated
        a₄
        lSize
        (shift
          (pointer-memory (shift (shift a i₄) zeroZ))
          zeroZ)
        lSize)) →
  ValidRD allocation (shift a₂ zeroZ) lSize

is-core-idle-call-find-next-bit-pre-2-goal8 : Set₁
is-core-idle-call-find-next-bit-pre-2-goal8 =
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
  Goal8
    lSize
    lIdleCpu
    lSchedGroupCpus
    lSchedGroupMask
    lGroupBalanceMask
    lCpuSmtMask
    region
    linked
