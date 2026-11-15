-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/sub_SubOld_wmpn_sub_nqtvc: the verification condition
-- for equal-length multiprecision subtraction into a separate result pointer,
-- including borrow propagation, memory updates, and frame preservation.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module sub_SubOld_wmpn_sub_nqtvc where

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

FunctionEq :
  {A B : Set} →
  (A → B) →
  (A → B) →
  Set
FunctionEq f g = (x : _) → f x ≡ g x

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
mapUpdatedAt newer older index newValue =
  FunctionEq (pelts newer) (update (pelts older) index newValue)

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

outsideUnchanged :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Int →
  Set
outsideUnchanged current original size =
  (j : Int) →
  (j <Z off current
   ∨ addInt (off current) size ≤Z j) →
  pelts current j ≡ pelts original j

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
valueEquation currentR x y size borrow =
  subtractInt
      (value currentR size)
      (multiplyInt
        (powerInt radixZ size)
        (unsignedZ borrow))
    ≡ subtractInt
        (value x size)
        (value y size)

loopInvariant :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Set
loopInvariant originalR x y size i borrow currentR =
  (zeroZ ≤Z signed32 i ∧ signed32 i ≤Z signed32 size)
  ∧ valueEquation currentR x y (signed32 i) borrow
  ∧ outsideUnchanged currentR originalR (signed32 size)
  ∧ borrowBounds borrow

subWithBorrowEquation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word64 →
  Word64 →
  Set
subWithBorrowEquation x y i inputBorrow result borrow =
  subtractInt
      (unsignedZ result)
      (multiplyInt radixZ (unsignedZ borrow))
    ≡ subtractInt
        (subtractInt
          (unsignedZ
            (pelts x
              (addInt (off x) (signed32 i))))
          (unsignedZ
            (pelts y
              (addInt (off y) (signed32 i)))))
        (unsignedZ inputBorrow)

decreases :
  Word32 →
  Word32 →
  Word32 →
  Set
decreases size current next =
  zeroZ ≤Z subtractInt (signed32 size) (signed32 current)
  ∧ subtractInt (signed32 size) (signed32 next)
      <Z subtractInt (signed32 size) (signed32 current)

nextInvariant :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Set
nextInvariant originalR x y size i nextI borrow currentR =
  decreases size i nextI
  ∧ loopInvariant originalR x y size nextI borrow currentR

afterWrite :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Set
afterWrite originalR x y size i borrow currentR =
  int32InBounds (addInt (signed32 i) oneZ)
  ∧
  ((nextI : Word32) →
    signed32 nextI ≡ addInt (signed32 i) oneZ →
    nextInvariant originalR x y size i nextI borrow currentR)

updatedState :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Word64 →
  Word64 →
  Set
updatedState originalR x y size i currentR result borrow =
  (nextR : Ptr _ Word64) →
  sameShape nextR currentR →
  (mapUpdatedAt
     nextR
     currentR
     (addInt (off nextR) (signed32 i))
     result
   ∧ pelts nextR (addInt (off nextR) (signed32 i))
       ≡ result) →
  afterWrite originalR x y size i borrow nextR

afterSubWithBorrow :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Word64 →
  Word64 →
  Set
afterSubWithBorrow originalR x y size i currentR result borrow =
  (accessAt currentR (addInt (off currentR) (signed32 i))
   ∧ writeable currentR ≡ true)
  ∧ updatedState originalR x y size i currentR result borrow

subWithBorrowStep :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Set
subWithBorrowStep originalR x y size i inputBorrow currentR =
  (result borrow : Word64) →
  (subWithBorrowEquation x y i inputBorrow result borrow
   ∧ borrowBounds borrow) →
  afterSubWithBorrow
    originalR x y size i currentR result borrow

bodyStep :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Set
bodyStep originalR x y size i inputBorrow currentR =
  accessAt x (addInt (off x) (signed32 i))
  ∧ accessAt y (addInt (off y) (signed32 i))
  ∧ borrowBounds inputBorrow
  ∧ subWithBorrowStep
      originalR x y size i inputBorrow currentR

finished :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Set
finished originalR x y size borrow currentR =
  borrowBounds borrow
  ∧ valueEquation currentR x y (signed32 size) borrow
  ∧ outsideUnchanged currentR originalR (signed32 size)

loopStep :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Set
loopStep originalR x y size i borrow currentR =
  IfSet
    (intLess (signed32 i) (signed32 size))
    (bodyStep originalR x y size i borrow currentR)
    (finished originalR x y size borrow currentR)

allLoopStates :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Set
allLoopStates originalR x y size =
  (i : Word32) →
  (borrow : Word64) →
  (currentR : Ptr _ Word64) →
  sameShape currentR originalR →
  loopInvariant originalR x y size i borrow currentR →
  loopStep originalR x y size i borrow currentR

initialVC :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Set
initialVC originalR x y size =
  zeroZ ≤Z zeroZ
  ∧ zeroZ ≤Z signed32 size
  ∧ subtractInt
      (value originalR zeroZ)
      (multiplyInt (powerInt radixZ zeroZ) zeroZ)
    ≡ subtractInt
        (value x zeroZ)
        (value y zeroZ)
  ∧ zeroZ ≤Z zeroZ
  ∧ zeroZ ≤Z oneZ
  ∧ allLoopStates originalR x y size

wmpn-sub-n'vc : Set₁
wmpn-sub-n'vc =
  (Zone : Set) →
  (x : Ptr Zone Word64) →
  (size : Word32) →
  (y : Ptr Zone Word64) →
  (result : Ptr Zone Word64) →
  valid x (signed32 size) →
  valid y (signed32 size) →
  valid result (signed32 size) →
  writeable result ≡ true →
  initialVC result x y size
