-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_assert_rte_signed_overflow_goal27:
-- under the stated integer-range, memory-validity, separation, framing,
-- linkedness, CPU-mask, havoc-update, and loop-state assumptions, the
-- branch-selected CPU index is at most 2147483646, preventing signed
-- 32-bit overflow on increment. This file contains no proof.

{-# OPTIONS --safe #-}

module should-we-balance-Why3-ide-VCshould-we-balance-assert-rte-signed-overflow-goal27 where

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

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) = negative (m * suc n)
multiplyInt (negsuc m) (pos n) = negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) = pos (suc m * suc n)

ifSet : Bool → Set → Set → Set
ifSet true yes _ = yes
ifSet false _ no = no

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

PointwiseEqual : (Addr → Int) → (Addr → Int) → Set
PointwiseEqual first-memory second-memory =
  (location : Addr) →
  first-memory location ≡ second-memory location

BranchState :
  Int →
  Bool →
  Bool →
  Int →
  Int →
  Addr →
  Addr →
  Int →
  Int →
  (Addr → Int) →
  (Addr → Int) →
  Int →
  (Addr → Addr) →
  Int →
  (Int → Int) →
  (Int → Addr) →
  (Int → Int) →
  Addr →
  Addr →
  Set
BranchState
  flag
  p₁
  p
  cpu
  fallback-cpu
  a₂
  a₁
  idle-value
  masked-value
  updated-memory
  current-memory
  lSize
  pointer-memory
  current-cpu
  lIdleCpu
  lCpuSmtMask
  allocation
  current-address
  next-address =
  ifSet
    (intEqual flag zeroZ)
    ((p₁ ≡ false) ∧ (cpu ≡ fallback-cpu))
    ((p ≡ false) ∧
      (p₁ ≡ true) ∧
      (a₂ ≡ a₁) ∧
      (idle-value ≠ zeroZ) ∧
      DivisibleByEight masked-value ∧
      PointwiseEqual updated-memory current-memory ∧
      Not
        (IdleCore
          lSize
          lIdleCpu
          lCpuSmtMask
          pointer-memory
          current-memory
          current-cpu) ∧
      ValidRD allocation current-address oneZ ∧
      ValidRD allocation next-address oneZ)

SelectedBound : Bool → Int → Int → Set
SelectedBound true cpu _ = cpu ≤Z signed32MaximumMinusOne
SelectedBound false _ fallback-cpu =
  fallback-cpu ≤Z signed32MaximumMinusOne

Goal27 :
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
Goal27
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
  (cpu : Int) →
  (a₁ : Addr) →
  (integer-memory : Addr → Int) →
  (pointer-memory : Addr → Addr) →
  (a : Addr) →
  (array-index : Int) →
  (a₂ : Addr) →
  (current-memory : Addr → Int) →
  (integer-memory₁ integer-memory₂ : Addr → Int) →
  (chosen-cpu limit flag : Int) →
  (allocation : Int → Int) →
  (fallback-cpu : Int) →
  (p₁ p : Bool) →
  let
    idle-value = lIdleCpu cpu
    a₃ = shift a₁ threeZ
    x₁ = integer-memory a₃
    a₄ = shift a₁ fourZ
    a₅ = pointer-memory a₄
    a₆ = shift a₅ zeroZ
    a₇ = pointer-memory a₆
    a₈ = shift a₁ oneZ
    x₂ = integer-memory a₈
    x₃ = integer-memory (shift a₇ x₂)
    a₉ = shift a₁ zeroZ
    a₁₀ = shift a array-index
    a₁₁ = pointer-memory a₉
    a₁₂ = shift a₁₁ oneZ
    a₁₃ = shift a₂ zeroZ
    a₁₄ = shift (pointer-memory a₁₃) oneZ
    x₄ = current-memory a₁₄
    a₁₅ = shift a₁₀ zeroZ
    a₁₆ = shift a₁₁ zeroZ
    a₁₇ = pointer-memory a₁₆
    a₁₈ = lGroupBalanceMask a₁₇
    a₁₉ = pointer-memory a₁₅
    a₂₀ = shift a₁₉ zeroZ
    a₂₁ = shift a₇ zeroZ
    a₂₂ =
      havoc havoc-theory
        integer-memory₁
        integer-memory
        a₂₀
        lSize
    a₂₃ = pointer-memory (shift a₁₈ zeroZ)
    a₂₄ =
      havoc havoc-theory
        integer-memory₂
        integer-memory
        a₂₀
        lSize
    a₂₅ = a₂₄ (shift a₁₉ cpu)
    a₂₆ = a₂₄ (shift a₇ chosen-cpu)
    a₂₇ = a₂₄ (shift a₇ cpu)
    a₂₈ = a₂₄ (shift a₂₃ chosen-cpu)
    a₂₉ = a₂₄ a₁₂
    a₃₀ = shift a₂₃ zeroZ
    lower-bound = toUint32 conversion limit
  in
  ((idle-value ≠ zeroZ) ↔ (flag ≠ zeroZ)) →
  x₁ ≠ twoZ →
  x₃ ≠ zeroZ →
  zeroZ ≤Z array-index →
  array-index <Z lSize →
  zeroZ ≤Z cpu →
  cpu <Z lSize →
  zeroZ ≤Z limit →
  limit ≤Z lSize →
  toUint32 conversion cpu <Z lSize →
  zeroZ ≤Z x₂ →
  x₂ <Z lSize →
  region (base a) ≤Z zeroZ →
  region (base a₁) ≤Z zeroZ →
  Framed region pointer-memory →
  linked allocation →
  IsUint8 flag →
  IsUint32 array-index →
  IsSint32 chosen-cpu →
  IsSint32 fallback-cpu →
  IsSint32 cpu →
  IsSint32 limit →
  ValidRD allocation a₁ fiveZ →
  IsUint32 x₁ →
  IsSint32 x₂ →
  ValidRD allocation a₄ oneZ →
  ValidRD allocation a₈ oneZ →
  ValidRD allocation a₃ oneZ →
  ValidRD allocation a₉ oneZ →
  ValidRD allocation a₁₀ oneZ →
  ValidRD allocation a₅ oneZ →
  ValidRD allocation (pointer-memory (shift a₁ twoZ)) twoZ →
  ValidRD allocation a₁₁ twoZ →
  IsSint32 (integer-memory a₁₂) →
  IsSint32 x₄ →
  ValidRD allocation a₁₅ oneZ →
  ValidRD allocation a₆ oneZ →
  ValidRD allocation a₁₆ oneZ →
  ValidRD allocation a₁₇ oneZ →
  ValidRD allocation a₁₈ oneZ →
  IsUint8 x₃ →
  ValidRD allocation a₂₀ lSize →
  ValidRD allocation a₂₁ lSize →
  ValidRW allocation a₂₀ lSize →
  IsUint8 (a₂₂ (shift a₇ minusOneZ)) →
  IsUint8 (a₂₂ (shift a₂₃ minusOneZ)) →
  IsUint8 a₂₅ →
  IsUint8 a₂₆ →
  IsUint8 a₂₇ →
  IsUint8 a₂₈ →
  IsSint32 (a₂₂ a₁₂) →
  IsSint32 a₂₉ →
  ValidRD allocation a₃₀ lSize →
  Separated a₂₀ lSize a₃₀ lSize →
  BranchState
    flag
    p₁
    p
    cpu
    fallback-cpu
    a₂
    a₁
    idle-value
    x₄
    a₂₄
    current-memory
    lSize
    pointer-memory
    cpu
    lIdleCpu
    lCpuSmtMask
    allocation
    a₁₃
    a₁₄ →
  (LandSevenNonzero a₂₉ → chosen-cpu ≡ minusOneZ) →
  (chosen-cpu ≠ minusOneZ →
    lIdleCpu chosen-cpu ≠ zeroZ ∧
    a₂₆ ≠ zeroZ ∧
    a₂₈ ≠ zeroZ ∧
    zeroZ ≤Z chosen-cpu ∧
    chosen-cpu <Z lSize) →
  (chosen-cpu ≡ minusOneZ →
    ((index : Int) →
      a₂₄ (shift a₂₃ index) ≠ zeroZ →
      zeroZ ≤Z index →
      index <Z lSize →
      a₂₄ (shift a₁₉ index) ≠ zeroZ)) →
  (HasActiveFrom a₂₄ a₁₉ a₇ lower-bound lSize →
    lower-bound ≤Z cpu) →
  (HasActiveFrom a₂₄ a₁₉ a₇ lower-bound lSize →
    a₂₅ ≠ zeroZ ∧
    a₂₇ ≠ zeroZ) →
  (((index : Int) →
      index <Z lSize →
      lower-bound ≤Z index →
      Either
        (a₂₄ (shift a₁₉ index) ≡ zeroZ)
        (a₂₄ (shift a₇ index) ≡ zeroZ)) →
    lSize ≡ cpu) →
  (chosen-cpu ≠ minusOneZ →
    ((index : Int) →
      a₂₄ (shift a₇ index) ≠ zeroZ →
      a₂₄ (shift a₂₃ index) ≠ zeroZ →
      zeroZ ≤Z index →
      index <Z chosen-cpu →
      index <Z lSize →
      lIdleCpu index ≡ zeroZ)) →
  (chosen-cpu ≡ minusOneZ →
    ((index : Int) →
      a₂₄ (shift a₇ index) ≠ zeroZ →
      a₂₄ (shift a₂₃ index) ≠ zeroZ →
      zeroZ ≤Z index →
      index <Z limit →
      index <Z lSize →
      lIdleCpu index ≡ zeroZ)) →
  (HasActiveFrom a₂₄ a₁₉ a₇ lower-bound lSize →
    ((index : Int) →
      index <Z cpu →
      lower-bound ≤Z index →
      Either
        (a₂₄ (shift a₁₉ index) ≡ zeroZ)
        (a₂₄ (shift a₇ index) ≡ zeroZ))) →
  (chosen-cpu ≠ minusOneZ →
    ((index : Int) →
      a₂₄ (shift a₇ index) ≠ zeroZ →
      a₂₄ (shift a₂₃ index) ≠ zeroZ →
      zeroZ ≤Z index →
      chosen-cpu ≤Z index →
      index <Z limit →
      index <Z lSize →
      Not
        (IdleCore
          lSize
          lIdleCpu
          lCpuSmtMask
          pointer-memory
          a₂₄
          index))) →
  (chosen-cpu ≠ minusOneZ →
    ((index : Int) →
      a₂₄ (shift a₂₃ index) ≠ zeroZ →
      zeroZ ≤Z index →
      index <Z lSize →
      Either
        (a₂₄ (shift a₁₉ index) ≠ zeroZ)
        (Not
          (IdleCore
            lSize
            lIdleCpu
            lCpuSmtMask
            pointer-memory
            a₂₄
            index)))) →
  Either (flag ≡ zeroZ) (flag ≡ oneZ) →
  ((index : Int) →
    zeroZ ≤Z index →
    index <Z lSize →
    Separated
      a₂₁
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
    ((a₂₂ (shift a₂₃ index) ≠ zeroZ) ↔
      (a₂₂ (shift a₁₉ index) ≠ zeroZ))) →
  ((index : Int) →
    a₂₄ (shift a₁₉ index) ≠ zeroZ →
    zeroZ ≤Z index →
    index <Z lSize →
    a₂₄ (shift a₂₃ index) ≠ zeroZ) →
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
  SelectedBound p₁ cpu fallback-cpu

should-we-balance-assert-rte-signed-overflow-goal27 : Set₁
should-we-balance-assert-rte-signed-overflow-goal27 =
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
  Goal27
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
