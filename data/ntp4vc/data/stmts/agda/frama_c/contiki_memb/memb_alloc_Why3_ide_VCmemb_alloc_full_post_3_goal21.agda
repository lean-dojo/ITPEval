-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/contiki_memb/memb_alloc_Why3_ide_VCmemb_alloc_full_post_3_goal21:
-- under the stated integer bounds, memory-validity, framing, linkedness,
-- constancy, valid-member, full-pool, and preceding-occupancy assumptions,
-- the computed member address is the null address. This file contains no
-- proof.

{-# OPTIONS --safe #-}

module memb-alloc-Why3-ide-VCmemb-alloc-full-post-3-goal21 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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

zeroZ oneZ twoZ threeZ fourZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))
threeZ = pos (suc (suc (suc zero)))
fourZ = pos (suc (suc (suc (suc zero))))

signed32Lower signed32Upper uint16Upper signed32Maximum : Int
signed32Lower = negsuc 2147483647
signed32Upper = pos 2147483648
uint16Upper = pos 65536
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
Framed region pointerMemory =
  (p : Addr) →
  region (base (pointerMemory p)) ≤Z zeroZ

IsSint32 : Int → Set
IsSint32 x =
  (signed32Lower ≤Z x) ∧
  (x <Z signed32Upper)

IsUint16 : Int → Set
IsUint16 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint16Upper)

PValidMemb :
  (Int → Int) →
  (Addr → Addr) →
  (Addr → Int) →
  Addr →
  Set
PValidMemb allocation pointerMemory integerMemory m =
  let
    element-size = integerMemory (shift m zeroZ)
    element-count = integerMemory (shift m oneZ)
    total-size = multiplyInt element-count element-size
    status-array = pointerMemory (shift m twoZ)
    elements-array = pointerMemory (shift m threeZ)
    status-start = shift status-array zeroZ
    elements-start = shift elements-array zeroZ
  in
  (zeroZ <Z element-size) ∧
  (total-size ≤Z signed32Maximum) ∧
  ValidRW allocation m fourZ ∧
  ValidRW allocation status-array oneZ ∧
  ValidRW allocation elements-array oneZ ∧
  ValidRW allocation status-start element-count ∧
  ValidRW allocation elements-start total-size ∧
  Separated status-start element-count elements-start total-size

PFullMemb :
  (Addr → Addr) →
  (Addr → Int) →
  (Addr → Int) →
  Addr →
  Set
PFullMemb pointerMemory charMemory integerMemory m =
  (index : Int) →
  zeroZ ≤Z index →
  index <Z integerMemory (shift m oneZ) →
  charMemory
    (shift (pointerMemory (shift m twoZ)) index)
    ≠ zeroZ

Goal21 :
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal21 region linked sconst =
  (a : Addr) →
  (pointerMemory : Addr → Addr) →
  (i : Int) →
  (integerMemory : Addr → Int) →
  (charMemory : Addr → Int) →
  (allocation : Int → Int) →
  let
    pointer-location = shift a twoZ
    status-array = pointerMemory pointer-location
    status-location = shift status-array i
    count-location = shift a oneZ
    element-count = integerMemory count-location
    size-location = shift a zeroZ
    element-size = integerMemory size-location
    byte-offset = multiplyInt i element-size
    elements-location = shift a threeZ
    elements-array = pointerMemory elements-location
  in
  charMemory status-location ≡ zeroZ →
  zeroZ ≤Z i →
  i <Z element-count →
  region (base a) ≤Z zeroZ →
  signed32Lower ≤Z byte-offset →
  byte-offset ≤Z signed32Maximum →
  Framed region pointerMemory →
  linked allocation →
  sconst charMemory →
  IsSint32 i →
  IsUint16 element-count →
  IsUint16 element-size →
  PValidMemb allocation pointerMemory integerMemory a →
  PFullMemb pointerMemory charMemory integerMemory a →
  ValidRD allocation pointer-location oneZ →
  ValidRD allocation elements-location oneZ →
  ValidRD allocation count-location oneZ →
  ValidRD allocation size-location oneZ →
  ValidRD allocation status-location oneZ →
  ValidRW allocation status-location oneZ →
  ((prior-index : Int) →
    zeroZ ≤Z prior-index →
    prior-index <Z i →
    charMemory (shift status-array prior-index) ≠ zeroZ) →
  shift elements-array byte-offset ≡ addr zeroZ zeroZ

memb-alloc-full-post-3-goal21 : Set₁
memb-alloc-full-post-3-goal21 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal21 region linked sconst
