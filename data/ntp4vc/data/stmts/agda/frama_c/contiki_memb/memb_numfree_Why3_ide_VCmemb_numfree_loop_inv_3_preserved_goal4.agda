-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/contiki_memb/memb_numfree_Why3_ide_VCmemb_numfree_loop_inv_3_preserved_goal4:
-- under the stated loop-index, occurrence-count, integer-range, memory-validity,
-- framing, linkedness, constancy, and valid-member assumptions, advancing the
-- scan by one makes the free-member occurrence count equal the updated loop
-- count. This file contains no proof.

{-# OPTIONS --safe #-}

module memb-numfree-Why3-ide-VCmemb-numfree-loop-inv-3-preserved-goal4 where

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

negateInt : Int → Int
negateInt (pos n) = negative n
negateInt (negsuc n) = pos (suc n)

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

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

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

signed8Lower signed8Upper signed32Lower signed32Upper : Int
signed8Lower = negsuc 127
signed8Upper = pos 128
signed32Lower = negsuc 2147483647
signed32Upper = pos 2147483648

uint16Upper signed32Maximum signed32MaximumMinusOne : Int
uint16Upper = pos 65536
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

IsSint8 : Int → Set
IsSint8 x =
  (signed8Lower ≤Z x) ∧
  (x <Z signed8Upper)

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
PValidMemb allocation pointer-memory integer-memory m =
  let
    element-size = integer-memory (shift m zeroZ)
    element-count = integer-memory (shift m oneZ)
    total-size = multiplyInt element-count element-size
    status-array = pointer-memory (shift m twoZ)
    elements-array = pointer-memory (shift m threeZ)
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

record OccArrayTheory : Set where
  field
    lOccA : (Addr → Int) → Int → Addr → Int → Int → Int

    end-occ :
      (upper lower : Int) →
      (memory : Addr → Int) →
      (element : Int) →
      (start : Addr) →
      upper ≤Z lower →
      lOccA memory element start lower upper ≡ zeroZ

    iter-occ-true :
      (upper : Int) →
      (memory : Addr → Int) →
      (start : Addr) →
      (element lower : Int) →
      memory (shift start (subtractInt upper oneZ)) ≡ element →
      lower <Z upper →
      addInt oneZ
        (lOccA memory element start lower (subtractInt upper oneZ))
        ≡
      lOccA memory element start lower upper

    iter-occ-false :
      (upper : Int) →
      (memory : Addr → Int) →
      (start : Addr) →
      (element lower : Int) →
      memory (shift start (subtractInt upper oneZ)) ≠ element →
      lower <Z upper →
      lOccA memory element start lower (subtractInt upper oneZ)
        ≡
      lOccA memory element start lower upper

open OccArrayTheory

IfZero : Int → Set → Set → Set
IfZero (pos zero) when-zero when-nonzero = when-zero
IfZero (pos (suc _)) when-zero when-nonzero = when-nonzero
IfZero (negsuc _) when-zero when-nonzero = when-nonzero

Goal4 :
  OccArrayTheory →
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal4 occurrence-theory region linked sconst =
  (a : Addr) →
  (integer-memory : Addr → Int) →
  (pointer-memory : Addr → Addr) →
  (char-memory : Addr → Int) →
  (index : Int) →
  (allocation : Int → Int) →
  (old-count new-count : Int) →
  let
    count-location = shift a oneZ
    element-count = integer-memory count-location
    pointer-location = shift a twoZ
    status-array = pointer-memory pointer-location
    occurrence-count =
      lOccA occurrence-theory
        char-memory
        zeroZ
        status-array
        zeroZ
        index
    next-index = addInt oneZ index
    status-location = shift status-array index
    status-value = char-memory status-location
  in
  zeroZ ≤Z index →
  index <Z element-count →
  index ≤Z element-count →
  region (base a) ≤Z zeroZ →
  occurrence-count ≤Z index →
  index ≤Z signed32MaximumMinusOne →
  Framed region pointer-memory →
  linked allocation →
  sconst char-memory →
  IsSint32 old-count →
  IsSint32 new-count →
  IsSint32 index →
  IsUint16 element-count →
  IsSint32 next-index →
  PValidMemb allocation pointer-memory integer-memory a →
  ValidRD allocation pointer-location oneZ →
  ValidRD allocation count-location oneZ →
  IsSint8 status-value →
  ValidRD allocation status-location oneZ →
  IsSint32 occurrence-count →
  IfZero
    status-value
    ((addInt oneZ old-count ≡ new-count) ∧
      (occurrence-count ≡ old-count) ∧
      (old-count ≤Z signed32MaximumMinusOne))
    (occurrence-count ≡ new-count) →
  lOccA occurrence-theory
    char-memory
    zeroZ
    status-array
    zeroZ
    next-index
    ≡
  new-count

memb-numfree-loop-inv-3-preserved-goal4 : Set₁
memb-numfree-loop-inv-3-preserved-goal4 =
  (occurrence-theory : OccArrayTheory) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal4 occurrence-theory region linked sconst
