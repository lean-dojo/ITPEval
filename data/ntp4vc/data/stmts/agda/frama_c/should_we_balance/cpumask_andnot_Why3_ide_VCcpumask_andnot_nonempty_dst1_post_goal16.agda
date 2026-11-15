-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/should_we_balance/cpumask_andnot_Why3_ide_VCcpumask_andnot_nonempty_dst1_post_goal16:
-- under the stated integer bounds, memory-validity, separation, framing,
-- linkedness, havoc-update, and cpumask-loop assumptions, membership in the
-- destination mask at index i_1 is characterized by the source masks.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module cpumask_andnot_Why3_ide_VCcpumask_andnot_nonempty_dst1_post_goal16 where

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

uint8Upper uint32Upper signed32Maximum : Int
uint8Upper = pos 256
uint32Upper = pos 4294967296
signed32Maximum = pos 2147483647

signed32Lower signed32Upper : Int
signed32Lower = negsuc 2147483647
signed32Upper = pos 2147483648

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

zeroAddr : Addr
zeroAddr = addr zeroZ zeroZ

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

Goal16 :
  Uint32Projection →
  HavocTheory →
  Int →
  (Int → Addr) →
  (Int → Int) →
  ((Int → Int) → Set) →
  Set
Goal16 conversion havoc-theory lSize lCpuSmtMask region linked =
  (pointer-memory : Addr → Addr) →
  (a a₁ a₂ : Addr) →
  (integer-memory₁ integer-memory₂ : Addr → Int) →
  (i i₁ : Int) →
  (allocation : Int → Int) →
  let
    a₃ = pointer-memory (shift a zeroZ)
    a₄ = shift a₃ zeroZ
    a₅ = pointer-memory (shift a₁ zeroZ)
    a₆ = shift a₅ zeroZ
    a₇ = pointer-memory (shift a₂ zeroZ)
    a₈ = shift a₇ zeroZ
    a₉ =
      havoc havoc-theory
        integer-memory₁
        integer-memory₂
        a₈
        lSize
  in
  zeroAddr ≠ a₂ →
  toUint32 conversion i ≡ lSize →
  zeroZ ≤Z i →
  zeroZ ≤Z i₁ →
  i₁ <Z lSize →
  i ≤Z lSize →
  region (base a) ≤Z zeroZ →
  region (base a₁) ≤Z zeroZ →
  region (base a₂) ≤Z zeroZ →
  Framed region pointer-memory →
  linked allocation →
  IsSint32 i →
  ValidRD allocation a oneZ →
  ValidRD allocation a₁ oneZ →
  ValidRD allocation a₂ oneZ →
  ValidRD allocation a₄ lSize →
  ValidRD allocation a₆ lSize →
  ValidRW allocation a₈ lSize →
  (a₂ ≠ a → Separated a₈ lSize a₄ lSize) →
  (a₂ ≠ a₁ → Separated a₈ lSize a₆ lSize) →
  ((i₂ : Int) →
    zeroZ ≤Z i₂ →
    i₂ <Z lSize →
    Separated
      a₈
      lSize
      (shift (pointer-memory (shift (lCpuSmtMask i₂) zeroZ)) zeroZ)
      lSize) →
  ((i₂ : Int) →
    let a₁₀ = shift a₇ i₂
    in
    i ≤Z i₂ →
    i₂ <Z lSize →
    (a₉ a₁₀ ≠ zeroZ) ↔ (integer-memory₂ a₁₀ ≠ zeroZ)) →
  ((i₂ : Int) →
    zeroZ ≤Z i₂ →
    i₂ <Z i →
    ((integer-memory₂ (shift a₃ i₂) ≡ zeroZ) ∧
      (integer-memory₂ (shift a₅ i₂) ≠ zeroZ))
      ↔
    (a₉ (shift a₇ i₂) ≠ zeroZ)) →
  ((integer-memory₂ (shift a₃ i₁) ≡ zeroZ) ∧
    (integer-memory₂ (shift a₅ i₁) ≠ zeroZ))
    ↔
  (a₉ (shift a₇ i₁) ≠ zeroZ)

cpumask-andnot-nonempty-dst1-post-goal16 : Set₁
cpumask-andnot-nonempty-dst1-post-goal16 =
  (conversion : Uint32Projection) →
  (havoc-theory : HavocTheory) →
  (lSize : Int) →
  ((zeroZ <Z lSize) ∧ (lSize ≤Z signed32Maximum)) →
  (lIdleCpu : Int → Int) →
  (lCpuSmtMask : Int → Addr) →
  (cpu-mask-theory : CpuMaskTheory lSize lIdleCpu lCpuSmtMask) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  Goal16
    conversion
    havoc-theory
    lSize
    lCpuSmtMask
    region
    linked
