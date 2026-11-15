-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_loop_inv_i5_preserved_goal21:
-- under the stated integer-range, memory-validity, separation, framing,
-- linkedness, CPU-mask, havoc-update, and loop-invariant assumptions, the
-- candidate CPU at index i_5 is not an idle core. This file contains no proof.

{-# OPTIONS --safe #-}

module should-we-balance-Why3-ide-VCshould-we-balance-loop-inv-i5-preserved-goal21 where

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
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  (Addr → Int) →
  (Addr → Int) →
  Int →
  (Addr → Addr) →
  (Int → Int) →
  (Int → Addr) →
  (Int → Int) →
  Addr →
  Set
BranchState
  flag
  p
  previous-cpu
  selected-cpu
  lower-start
  current-cpu
  idle-value
  masked-value
  updated-memory
  current-memory
  lSize
  pointer-memory
  lIdleCpu
  lCpuSmtMask
  allocation
  current-address =
  ifSet
    (intEqual flag zeroZ)
    ((lower-start ≡ selected-cpu) ∧
      (current-cpu ≤Z signed32MaximumMinusOne))
    ((p ≡ false) ∧
      (previous-cpu ≡ selected-cpu) ∧
      (idle-value ≠ zeroZ) ∧
      DivisibleByEight masked-value ∧
      PointwiseEqual updated-memory current-memory ∧
      (current-cpu ≤Z signed32MaximumMinusOne) ∧
      Not
        (IdleCore
          lSize
          lIdleCpu
          lCpuSmtMask
          pointer-memory
          current-memory
          current-cpu) ∧
      ValidRD allocation current-address oneZ ∧
      ifSet
        (intEqual previous-cpu minusOneZ)
        (current-cpu ≡ lower-start)
        (lower-start ≡ previous-cpu))

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

Goal21 :
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
Goal21
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
  (current-cpu : Int) →
  (a₁ : Addr) →
  (integer-memory : Addr → Int) →
  (pointer-memory : Addr → Addr) →
  (a : Addr) →
  (array-index : Int) →
  (integer-memory₂ integer-memory₁ : Addr → Int) →
  (selected-cpu limit lower-start flag target-cpu : Int) →
  (allocation : Int → Int) →
  (previous-cpu : Int) →
  (p : Bool) →
  (current-memory : Addr → Int) →
  let
    idle-value = lIdleCpu current-cpu
    a₂ = shift a₁ threeZ
    status = integer-memory a₂
    a₃ = shift a₁ fourZ
    a₄ = pointer-memory a₃
    a₅ = shift a₄ zeroZ
    a₆ = pointer-memory a₅
    a₇ = shift a₁ oneZ
    mask-index = integer-memory a₇
    selected-value = integer-memory (shift a₆ mask-index)
    a₈ = shift a array-index
    a₉ = shift a₈ zeroZ
    a₁₀ = pointer-memory a₉
    a₁₁ = shift a₁₀ zeroZ
    updated-memory =
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
    previous-memory =
      havoc havoc-theory
        integer-memory₁
        integer-memory
        a₁₁
        lSize
    current-first = updated-memory (shift a₁₀ current-cpu)
    selected-second = updated-memory (shift a₆ selected-cpu)
    current-second = updated-memory (shift a₆ current-cpu)
    selected-third = updated-memory (shift a₁₈ selected-cpu)
    masked-value = updated-memory a₁₉
    a₂₇ = shift a₁₈ zeroZ
    lower-bound = toUint32 conversion limit
  in
  lower-start ≠ minusOneZ →
  ((idle-value ≠ zeroZ) ↔ (flag ≠ zeroZ)) →
  status ≠ twoZ →
  selected-value ≠ zeroZ →
  updated-memory (shift a₆ target-cpu) ≠ zeroZ →
  updated-memory (shift a₁₈ target-cpu) ≠ zeroZ →
  zeroZ ≤Z array-index →
  array-index <Z lSize →
  zeroZ ≤Z target-cpu →
  lower-start ≤Z target-cpu →
  target-cpu <Z lSize →
  zeroZ ≤Z current-cpu →
  target-cpu ≤Z current-cpu →
  current-cpu <Z lSize →
  zeroZ ≤Z limit →
  limit ≤Z lSize →
  toUint32 conversion current-cpu <Z lSize →
  zeroZ ≤Z mask-index →
  mask-index <Z lSize →
  region (base a) ≤Z zeroZ →
  region (base a₁) ≤Z zeroZ →
  Framed region pointer-memory →
  linked allocation →
  IsUint8 flag →
  IsUint32 array-index →
  IsSint32 selected-cpu →
  IsSint32 previous-cpu →
  IsSint32 lower-start →
  IsSint32 current-cpu →
  IsSint32 limit →
  ValidRD allocation a₁ fiveZ →
  IsUint32 status →
  IsSint32 (addInt oneZ current-cpu) →
  IsSint32 mask-index →
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
  IsUint8 selected-value →
  ValidRD allocation a₁₁ lSize →
  ValidRD allocation a₂₀ lSize →
  ValidRW allocation a₁₁ lSize →
  IsUint8 (previous-memory (shift a₆ minusOneZ)) →
  IsUint8 (previous-memory (shift a₁₈ minusOneZ)) →
  IsUint8 current-first →
  IsUint8 selected-second →
  IsUint8 (updated-memory (shift a₆ lower-start)) →
  IsUint8 current-second →
  IsUint8 selected-third →
  IsUint8 (updated-memory (shift a₁₈ lower-start)) →
  IsSint32 (previous-memory a₁₉) →
  IsSint32 masked-value →
  ValidRD allocation a₂₇ lSize →
  Separated a₁₁ lSize a₂₇ lSize →
  BranchState
    flag
    p
    previous-cpu
    selected-cpu
    lower-start
    current-cpu
    idle-value
    (current-memory a₁₉)
    updated-memory
    current-memory
    lSize
    pointer-memory
    lIdleCpu
    lCpuSmtMask
    allocation
    a₁₉ →
  (LandSevenNonzero masked-value →
    selected-cpu ≡ minusOneZ) →
  (selected-cpu ≠ minusOneZ →
    lIdleCpu selected-cpu ≠ zeroZ ∧
    selected-second ≠ zeroZ ∧
    selected-third ≠ zeroZ ∧
    zeroZ ≤Z selected-cpu ∧
    selected-cpu <Z lSize) →
  (selected-cpu ≡ minusOneZ →
    ((index : Int) →
      updated-memory (shift a₁₈ index) ≠ zeroZ →
      zeroZ ≤Z index →
      index <Z lSize →
      updated-memory (shift a₁₀ index) ≠ zeroZ)) →
  (HasActiveFrom
      updated-memory
      a₁₀
      a₆
      lower-bound
      lSize →
    lower-bound ≤Z current-cpu) →
  (HasActiveFrom
      updated-memory
      a₁₀
      a₆
      lower-bound
      lSize →
    current-first ≠ zeroZ ∧
    current-second ≠ zeroZ) →
  (((index : Int) →
      index <Z lSize →
      lower-bound ≤Z index →
      Either
        (updated-memory (shift a₁₀ index) ≡ zeroZ)
        (updated-memory (shift a₆ index) ≡ zeroZ)) →
    lSize ≡ current-cpu) →
  (selected-cpu ≠ minusOneZ →
    ((index : Int) →
      updated-memory (shift a₆ index) ≠ zeroZ →
      updated-memory (shift a₁₈ index) ≠ zeroZ →
      zeroZ ≤Z index →
      index <Z selected-cpu →
      index <Z lSize →
      lIdleCpu index ≡ zeroZ)) →
  (selected-cpu ≡ minusOneZ →
    ((index : Int) →
      updated-memory (shift a₆ index) ≠ zeroZ →
      updated-memory (shift a₁₈ index) ≠ zeroZ →
      zeroZ ≤Z index →
      index <Z limit →
      index <Z lSize →
      lIdleCpu index ≡ zeroZ)) →
  (HasActiveFrom
      updated-memory
      a₁₀
      a₆
      lower-bound
      lSize →
    ((index : Int) →
      index <Z current-cpu →
      lower-bound ≤Z index →
      Either
        (updated-memory (shift a₁₀ index) ≡ zeroZ)
        (updated-memory (shift a₆ index) ≡ zeroZ))) →
  (selected-cpu ≠ minusOneZ →
    ((index : Int) →
      updated-memory (shift a₆ index) ≠ zeroZ →
      updated-memory (shift a₁₈ index) ≠ zeroZ →
      zeroZ ≤Z index →
      selected-cpu ≤Z index →
      index <Z limit →
      index <Z lSize →
      Not
        (IdleCore
          lSize
          lIdleCpu
          lCpuSmtMask
          pointer-memory
          updated-memory
          index))) →
  (selected-cpu ≠ minusOneZ →
    ((index : Int) →
      updated-memory (shift a₁₈ index) ≠ zeroZ →
      zeroZ ≤Z index →
      index <Z lSize →
      Either
        (updated-memory (shift a₁₀ index) ≠ zeroZ)
        (Not
          (IdleCore
            lSize
            lIdleCpu
            lCpuSmtMask
            pointer-memory
            updated-memory
            index)))) →
  Either (flag ≡ zeroZ) (flag ≡ oneZ) →
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
    ((previous-memory (shift a₁₈ index) ≠ zeroZ) ↔
      (previous-memory (shift a₁₀ index) ≠ zeroZ))) →
  ((index : Int) →
    updated-memory (shift a₁₀ index) ≠ zeroZ →
    zeroZ ≤Z index →
    index <Z lSize →
    updated-memory (shift a₁₈ index) ≠ zeroZ) →
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
  Not
    (IdleCore
      lSize
      lIdleCpu
      lCpuSmtMask
      pointer-memory
      updated-memory
      target-cpu)

should-we-balance-loop-invariant-i5-preserved-goal21 : Set₁
should-we-balance-loop-invariant-i5-preserved-goal21 =
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
  Goal21
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
