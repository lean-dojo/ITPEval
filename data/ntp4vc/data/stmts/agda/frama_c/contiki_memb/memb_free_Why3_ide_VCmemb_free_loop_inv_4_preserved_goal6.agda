-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/contiki_memb/memb_free_Why3_ide_VCmemb_free_loop_inv_4_preserved_goal6:
-- under the stated index bounds, memory-validity, framing, linkedness,
-- constancy, valid-member, and preceding-address assumptions, the member
-- pointer constructed at index 1 + i maps back to that index. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module memb-free-Why3-ide-VCmemb-free-loop-inv-4-preserved-goal6 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; div-helper)

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

natDivide : Nat → Nat → Nat
natDivide n zero = zero
natDivide n (suc m) = div-helper zero m n m

truncateDivide : Int → Int → Int
truncateDivide (pos n) (pos zero) = pos zero
truncateDivide (pos n) (pos (suc m)) =
  pos (natDivide n (suc m))
truncateDivide (pos n) (negsuc m) =
  negative (natDivide n (suc m))
truncateDivide (negsuc n) (pos zero) = pos zero
truncateDivide (negsuc n) (pos (suc m)) =
  negative (natDivide (suc n) (suc m))
truncateDivide (negsuc n) (negsuc m) =
  pos (natDivide (suc n) (suc m))

zeroZ oneZ twoZ threeZ fourZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))
threeZ = pos (suc (suc (suc zero)))
fourZ = pos (suc (suc (suc (suc zero))))

signed32Lower signed32Upper uint16Upper : Int
signed32Lower = negsuc 2147483647
signed32Upper = pos 2147483648
uint16Upper = pos 65536

signed32Maximum signed32MaximumMinusOne : Int
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

MembIndex :
  (Addr → Addr) →
  (Addr → Int) →
  Addr →
  Addr →
  Int
MembIndex pointer-memory integer-memory m pointer =
  truncateDivide
    (subtractInt
      (offset pointer)
      (offset (pointer-memory (shift m threeZ))))
    (integer-memory (shift m zeroZ))

MembPtr :
  (Addr → Addr) →
  (Addr → Int) →
  Addr →
  Int →
  Addr
MembPtr pointer-memory integer-memory m index =
  shift
    (pointer-memory (shift m threeZ))
    (multiplyInt index (integer-memory (shift m zeroZ)))

Goal6 :
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal6 region linked sconst =
  (pointer-memory : Addr → Addr) →
  (integer-memory : Addr → Int) →
  (memb : Addr) →
  (index : Int) →
  (member-address : Addr) →
  (allocation : Int → Int) →
  (char-memory : Addr → Int) →
  let
    current-pointer =
      MembPtr pointer-memory integer-memory memb index
    count-location = shift memb oneZ
    element-count = integer-memory count-location
    size-location = shift memb zeroZ
    element-size = integer-memory size-location
    next-index = addInt oneZ index
    elements-location = shift memb threeZ
  in
  current-pointer ≠ member-address →
  MembIndex pointer-memory integer-memory memb current-pointer ≡ index →
  zeroZ ≤Z index →
  index <Z element-count →
  index ≤Z element-count →
  region (base member-address) ≤Z zeroZ →
  region (base memb) ≤Z zeroZ →
  index ≤Z signed32MaximumMinusOne →
  Framed region pointer-memory →
  linked allocation →
  sconst char-memory →
  IsSint32 index →
  IsUint16 element-count →
  IsUint16 element-size →
  IsSint32 next-index →
  PValidMemb allocation pointer-memory integer-memory memb →
  ValidRD allocation elements-location oneZ →
  ValidRD allocation count-location oneZ →
  ValidRD allocation size-location oneZ →
  ((prior-index : Int) →
    zeroZ ≤Z prior-index →
    prior-index <Z index →
    shift
      (pointer-memory elements-location)
      (multiplyInt prior-index element-size)
      ≠ member-address) →
  next-index ≡
    MembIndex pointer-memory integer-memory memb
      (MembPtr pointer-memory integer-memory memb next-index)

memb-free-loop-inv-4-preserved-goal6 : Set₁
memb-free-loop-inv-4-preserved-goal6 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal6 region linked sconst
