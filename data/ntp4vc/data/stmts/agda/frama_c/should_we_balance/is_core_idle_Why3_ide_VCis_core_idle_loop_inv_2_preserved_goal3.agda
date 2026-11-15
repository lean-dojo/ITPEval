-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/should_we_balance/is_core_idle_Why3_ide_VCis_core_idle_loop_inv_2_preserved_goal3:
-- under the stated integer bounds, memory-validity, separation, framing,
-- linkedness, SMT-mask, and loop-invariant assumptions, the idle-CPU flag at
-- index i3 is nonzero. This file contains no proof.

{-# OPTIONS --safe #-}

module is-core-idle-Why3-ide-VCis-core-idle-loop-inv-2-preserved-goal3 where

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

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    evidence : P value

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

HasActiveFrom :
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Set
HasActiveFrom integer-memory mask lower upper =
  Exists Int λ index →
    integer-memory (shift mask index) ≠ zeroZ ∧
    index <Z upper ∧
    lower ≤Z index

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

Goal3 :
  Uint32Projection →
  Int →
  (Int → Int) →
  (Addr → Addr) →
  (Addr → Addr) →
  (Addr → Addr) →
  (Int → Addr) →
  (Int → Int) →
  ((Int → Int) → Set) →
  Set
Goal3
  conversion
  lSize
  lIdleCpu
  lSchedGroupCpus
  lSchedGroupMask
  lGroupBalanceMask
  lCpuSmtMask
  region
  linked =
  (i5 : Int) →
  (pointer-memory : Addr → Addr) →
  (integer-memory : Addr → Int) →
  (i4 i2 i3 i i1 : Int) →
  (a : Addr) →
  (allocation : Int → Int) →
  let
    a1 = shift (lCpuSmtMask i5) zeroZ
    a2 = pointer-memory a1
    x = integer-memory (shift a2 i4)
    x1 = toUint32 conversion i2
  in
  lIdleCpu i5 ≠ zeroZ →
  integer-memory (shift a2 i3) ≠ zeroZ →
  zeroZ ≤Z i →
  i <Z lSize →
  i3 ≤Z i1 →
  zeroZ ≤Z i2 →
  zeroZ ≤Z i3 →
  zeroZ ≤Z i5 →
  i5 <Z lSize →
  i2 ≤Z lSize →
  toUint32 conversion i4 <Z lSize →
  region (base a) ≤Z zeroZ →
  Framed region pointer-memory →
  linked allocation →
  IsUint32 i →
  IsSint32 i1 →
  IsSint32 i2 →
  IsSint32 i4 →
  IsSint32 i5 →
  IsSint32 (addInt oneZ i1) →
  ValidRD allocation a1 oneZ →
  IsUint8 x →
  ValidRD allocation (shift a2 zeroZ) lSize →
  IfSet
    (intEqual i5 i4)
    (i5 ≡ i1 ∧
      i5 ≤Z signed32MaximumMinusOne)
    (i4 ≡ i1 ∧
      lIdleCpu i4 ≠ zeroZ ∧
      zeroZ ≤Z i4 ∧
      i4 <Z lSize ∧
      i4 ≤Z signed32MaximumMinusOne) →
  (((index : Int) →
      index <Z lSize →
      x1 ≤Z index →
      integer-memory (shift a2 index) ≡ zeroZ) →
    lSize ≡ i4) →
  (HasActiveFrom integer-memory a2 x1 lSize →
    x ≠ zeroZ) →
  (HasActiveFrom integer-memory a2 x1 lSize →
    i4 <Z lSize) →
  (HasActiveFrom integer-memory a2 x1 lSize →
    i4 <Z lSize ∧
    x1 ≤Z i4) →
  (HasActiveFrom integer-memory a2 x1 lSize →
    ((index : Int) →
      index <Z i4 →
      x1 ≤Z index →
      integer-memory (shift a2 index) ≡ zeroZ)) →
  ((index : Int) →
    integer-memory (shift a2 index) ≠ zeroZ →
    zeroZ ≤Z index →
    index <Z i2 →
    lIdleCpu index ≠ zeroZ) →
  ((index : Int) →
    let a3 = shift a index
    in
    zeroZ ≤Z index →
    index <Z lSize →
    ValidRD allocation a3 oneZ ∧
    ValidRW
      allocation
      (shift (pointer-memory (shift a3 zeroZ)) zeroZ)
      lSize) →
  ((a3 : Addr) →
    let
      a4 = lSchedGroupCpus a3
      a5 = shift (pointer-memory (shift a4 zeroZ)) zeroZ
    in
    ValidRD allocation a4 oneZ ∧
    ValidRD allocation a5 lSize ∧
    ((index : Int) →
      zeroZ ≤Z index →
      index <Z lSize →
      Separated
        a5
        lSize
        (shift
          (pointer-memory (shift (shift a index) zeroZ))
          zeroZ)
        lSize)) →
  ((a3 : Addr) →
    let
      a4 = lSchedGroupMask a3
      a5 = shift (pointer-memory (shift a4 zeroZ)) zeroZ
    in
    ValidRD allocation a4 oneZ ∧
    ValidRD allocation a5 lSize ∧
    ((index : Int) →
      zeroZ ≤Z index →
      index <Z lSize →
      Separated
        a5
        lSize
        (shift
          (pointer-memory (shift (shift a index) zeroZ))
          zeroZ)
        lSize)) →
  ((a3 : Addr) →
    let
      a4 = lGroupBalanceMask a3
      a5 = shift (pointer-memory (shift a4 zeroZ)) zeroZ
    in
    ValidRD allocation a4 oneZ ∧
    ValidRD allocation a5 lSize ∧
    ((index : Int) →
      zeroZ ≤Z index →
      index <Z lSize →
      Separated
        a5
        lSize
        (shift
          (pointer-memory (shift (shift a index) zeroZ))
          zeroZ)
        lSize)) →
  ((index : Int) →
    let
      a3 = lCpuSmtMask index
      a4 = shift (pointer-memory (shift a3 zeroZ)) zeroZ
    in
    zeroZ ≤Z index →
    index <Z lSize →
    ValidRD allocation a3 oneZ ∧
    ValidRD allocation a4 lSize ∧
    ((other-index : Int) →
      zeroZ ≤Z other-index →
      other-index <Z lSize →
      Separated
        a4
        lSize
        (shift
          (pointer-memory (shift (shift a other-index) zeroZ))
          zeroZ)
        lSize)) →
  lIdleCpu i3 ≠ zeroZ

is-core-idle-loop-invariant-2-preserved-goal3 : Set₁
is-core-idle-loop-invariant-2-preserved-goal3 =
  (conversion : Uint32Projection) →
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
  Goal3
    conversion
    lSize
    lIdleCpu
    lSchedGroupCpus
    lSchedGroupMask
    lGroupBalanceMask
    lCpuSmtMask
    region
    linked
