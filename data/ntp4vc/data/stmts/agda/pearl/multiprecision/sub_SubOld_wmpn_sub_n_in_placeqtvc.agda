-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/sub_SubOld_wmpn_sub_n_in_placeqtvc: the verification
-- condition for equal-length in-place multiprecision subtraction, including
-- borrow propagation, pointer access, memory updates, and frame preservation.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module SubSubOldWmpnSubNInPlaceVC where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤Z_ _<Z_
infixr 5 _∷V_
infixr 3 _∧_
infixr 2 _∨_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

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
multiplyInt (pos m) (negsuc n) =
  negateInt (pos (m * suc n))
multiplyInt (negsuc m) (pos n) =
  negateInt (pos (suc m * n))
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc _) = zero

powerNat : Int → Nat → Int
powerNat base zero = pos 1
powerNat base (suc exponent) =
  multiplyInt base (powerNat base exponent)

powerInt : Int → Int → Int
powerInt base exponent = powerNat base (intToNat exponent)

zeroZ oneZ : Int
zeroZ = pos 0
oneZ = pos 1

min32 max32 radixZ : Int
min32 = negsuc 2147483647
max32 = pos 2147483647
radixZ = pos 18446744073709551616

int32InBounds : Int → Set
int32InBounds n = min32 ≤Z n ∧ n ≤Z max32

data Vec (A : Set) : Nat → Set where
  []V   : Vec A zero
  _∷V_  : {n : Nat} → A → Vec A n → Vec A (suc n)

bitValue : Bool → Nat
bitValue false = zero
bitValue true = 1

unsignedNat : {n : Nat} → Vec Bool n → Nat
unsignedNat []V = zero
unsignedNat (bit ∷V bits) =
  bitValue bit + 2 * unsignedNat bits

unsignedZ : {n : Nat} → Vec Bool n → Int
unsignedZ bits = pos (unsignedNat bits)

lastBit : {n : Nat} → Vec Bool (suc n) → Bool
lastBit {zero} (bit ∷V []V) = bit
lastBit {suc n} (_ ∷V bits) = lastBit bits

Word32 Word64 : Set
Word32 = Vec Bool 32
Word64 = Vec Bool 64

signed32 : Word32 → Int
signed32 bits with lastBit bits
... | false = pos (unsignedNat bits)
... | true =
  subtractInt (pos (unsignedNat bits)) (pos 4294967296)

record Ptr (Zone A : Set) : Set where
  constructor pointer
  field
    memory    : Int → A
    cellCount : Nat
    off       : Int
    lo        : Int
    hi        : Int
    writeable : Bool
    region    : Zone

open Ptr public

pelts : {Zone : Set} → Ptr Zone Word64 → Int → Word64
pelts p = memory p

plength : {Zone : Set} → Ptr Zone Word64 → Int
plength p = pos (cellCount p)

valid : {Zone : Set} → Ptr Zone Word64 → Int → Set
valid p size =
  int32InBounds size
  ∧ zeroZ ≤Z size
  ∧ (zeroZ ≤Z lo p ∧ lo p ≤Z off p)
  ∧ addInt (off p) size ≤Z hi p
  ∧ hi p ≤Z plength p

sameShape :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
sameShape newer older =
  cellCount newer ≡ cellCount older
  ∧ off newer ≡ off older
  ∧ lo newer ≡ lo older
  ∧ hi newer ≡ hi older
  ∧ writeable newer ≡ writeable older
  ∧ region newer ≡ region older

update :
  {A : Set} →
  (Int → A) →
  Int →
  A →
  Int →
  A
update f index value query with intEqual query index
... | true = value
... | false = f query

mapUpdatedAt :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Int →
  Word64 →
  Set
mapUpdatedAt newer older index value =
  (query : Int) →
  pelts newer query ≡ update (pelts older) index value query

valueFrom :
  {Zone : Set} →
  Ptr Zone Word64 →
  Int →
  Nat →
  Int
valueFrom p index zero = zeroZ
valueFrom p index (suc count) =
  addInt
    (unsignedZ (pelts p index))
    (multiplyInt
      radixZ
      (valueFrom p (addInt index oneZ) count))

value :
  {Zone : Set} →
  Ptr Zone Word64 →
  Int →
  Int
value p size =
  valueFrom p (off p) (intToNat size)

unchangedOutside :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Int →
  Set
unchangedOutside current original size =
  (j : Int) →
  (j <Z off current ∨
   addInt (off current) size ≤Z j) →
  pelts current j ≡ pelts original j

tailEqual :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Int →
  Int →
  Set
tailEqual current original from size =
  (j : Int) →
  (from ≤Z j ∧ j <Z size) →
  pelts current (addInt (off current) j)
    ≡ pelts original (addInt (off current) j)

accessAt :
  {Zone : Set} →
  Ptr Zone Word64 →
  Int →
  Set
accessAt p index =
  lo p ≤Z index ∧ index <Z hi p

borrowBounds : Word64 → Set
borrowBounds borrow =
  zeroZ ≤Z unsignedZ borrow
  ∧ unsignedZ borrow ≤Z oneZ

valueEquation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Int →
  Word64 →
  Set
valueEquation current original y size borrow =
  subtractInt
      (value current size)
      (multiplyInt
        (powerInt radixZ size)
        (unsignedZ borrow))
    ≡ subtractInt
        (value original size)
        (value y size)

loopInvariant :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Set
loopInvariant original y size i borrow current =
  (zeroZ ≤Z signed32 i ∧ signed32 i ≤Z signed32 size)
  ∧ valueEquation current original y (signed32 i) borrow
  ∧ borrowBounds borrow
  ∧ tailEqual current original (signed32 i) (signed32 size)
  ∧ unchangedOutside current original (signed32 size)

subWithBorrowEquation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word64 →
  Word64 →
  Set
subWithBorrowEquation current y i input-borrow result borrow =
  subtractInt
      (unsignedZ result)
      (multiplyInt radixZ (unsignedZ borrow))
    ≡ subtractInt
        (subtractInt
          (unsignedZ
            (pelts current
              (addInt (off current) (signed32 i))))
          (unsignedZ
            (pelts y
              (addInt (off y) (signed32 i)))))
        (unsignedZ input-borrow)

nextInvariant :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Set
nextInvariant original y size i next-i borrow current =
  (zeroZ ≤Z subtractInt (signed32 size) (signed32 i)
   ∧ subtractInt (signed32 size) (signed32 next-i)
       <Z subtractInt (signed32 size) (signed32 i))
  ∧ loopInvariant original y size next-i borrow current

afterWrite :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Set
afterWrite original y size i borrow current =
  int32InBounds (addInt (signed32 i) oneZ)
  ∧
  ((next-i : Word32) →
    signed32 next-i ≡ addInt (signed32 i) oneZ →
    nextInvariant original y size i next-i borrow current)

updatedState :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Word64 →
  Word64 →
  Set
updatedState original y size i current result borrow =
  (newer : Ptr _ Word64) →
  sameShape newer current →
  (mapUpdatedAt
     newer
     current
     (addInt (off newer) (signed32 i))
     result
   ∧ pelts newer (addInt (off newer) (signed32 i))
       ≡ result) →
  afterWrite original y size i borrow newer

afterSubWithBorrow :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Word64 →
  Word64 →
  Set
afterSubWithBorrow original y size i current result borrow =
  (accessAt current (addInt (off current) (signed32 i))
   ∧ writeable current ≡ true)
  ∧ updatedState original y size i current result borrow

subWithBorrowStep :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Set
subWithBorrowStep original y size i input-borrow current =
  (result borrow : Word64) →
  (subWithBorrowEquation
     current y i input-borrow result borrow
   ∧ borrowBounds borrow) →
  afterSubWithBorrow original y size i current result borrow

bodyStep :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Set
bodyStep original y size i input-borrow current =
  accessAt current (addInt (off current) (signed32 i))
  ∧ accessAt y (addInt (off y) (signed32 i))
  ∧ borrowBounds input-borrow
  ∧ subWithBorrowStep original y size i input-borrow current

finished :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Set
finished original y size borrow current =
  valueEquation current original y (signed32 size) borrow
  ∧ borrowBounds borrow
  ∧ unchangedOutside current original (signed32 size)

loopStep :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Set
loopStep original y size i borrow current =
  IfSet
    (intLess (signed32 i) (signed32 size))
    (bodyStep original y size i borrow current)
    (finished original y size borrow current)

allLoopStates :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Set
allLoopStates original y size =
  (i : Word32) →
  (borrow : Word64) →
  (current : Ptr _ Word64) →
  sameShape current original →
  loopInvariant original y size i borrow current →
  loopStep original y size i borrow current

initialVC :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Set
initialVC original y size =
  zeroZ ≤Z zeroZ
  ∧ zeroZ ≤Z signed32 size
  ∧ subtractInt
      (value original zeroZ)
      (multiplyInt (powerInt radixZ zeroZ) zeroZ)
    ≡ subtractInt
        (value original zeroZ)
        (value y zeroZ)
  ∧ zeroZ ≤Z zeroZ
  ∧ zeroZ ≤Z oneZ
  ∧ allLoopStates original y size

wmpn-sub-n-in-place'vc : Set₁
wmpn-sub-n-in-place'vc =
  (Zone : Set) →
  (size : Word32) →
  (original y : Ptr Zone Word64) →
  zeroZ ≤Z signed32 size →
  valid original (signed32 size) →
  valid y (signed32 size) →
  writeable original ≡ true →
  initialVC original y size
