-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/add_1_Add_1_wmpn_incr_1qtvc: the weakest-precondition
-- verification condition for incrementing a positive-length multiprecision
-- integer in place by one, including carry and memory-update obligations.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module AddOneAddOneWmpnIncrOneVC where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤Z_ _<Z_
infixr 5 _∷V_
infixr 3 _∧_
infixr 2 _∨_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A → B
    backward : B → A

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

subtractNat : Nat → Nat → Nat
subtractNat n zero = n
subtractNat zero (suc _) = zero
subtractNat (suc m) (suc n) = subtractNat m n

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

half : Nat → Nat
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

lowBit : Nat → Bool
lowBit zero = false
lowBit (suc zero) = true
lowBit (suc (suc n)) = lowBit n

natToVec : (width value : Nat) → Vec Bool width
natToVec zero value = []V
natToVec (suc width) value =
  lowBit value ∷V natToVec width (half value)

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

zero32 : Word32
zero32 = natToVec 32 0

zero64 one64 : Word64
zero64 = natToVec 64 0
one64 = natToVec 64 1

radixNat : Nat
radixNat = 18446744073709551616

modRadix : Nat → Nat
modRadix n with natLess n radixNat
... | true = n
... | false = subtractNat n radixNat

incrementModuloRadix : Word64 → Int
incrementModuloRadix x =
  pos (modRadix (unsignedNat x + 1))

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

FunctionEq :
  {A B : Set} →
  (A → B) →
  (A → B) →
  Set
FunctionEq f g = (x : _) → f x ≡ g x

peltsEq :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
peltsEq p q = FunctionEq (pelts p) (pelts q)

dataLengthEq :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
dataLengthEq p q = cellCount p ≡ cellCount q

dataEq :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
dataEq p q = dataLengthEq p q ∧ peltsEq p q

valid : {Zone : Set} → Ptr Zone Word64 → Int → Set
valid p size =
  int32InBounds size
  ∧ zeroZ ≤Z size
  ∧ (zeroZ ≤Z lo p ∧ lo p ≤Z off p)
  ∧ addInt (off p) size ≤Z hi p
  ∧ hi p ≤Z plength p

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
mapUpdatedAt newer older index limb =
  FunctionEq (pelts newer) (update (pelts older) index limb)

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

accessAt :
  {Zone : Set} →
  Ptr Zone Word64 →
  Int →
  Set
accessAt p index =
  lo p ≤Z index ∧ index <Z hi p

fullPointerShift :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Int →
  Set
fullPointerShift shifted base displacement =
  off shifted ≡ addInt (off base) displacement
  ∧ plength shifted ≡ plength base
  ∧ peltsEq shifted base
  ∧ dataEq shifted base
  ∧ lo shifted ≡ lo base
  ∧ hi shifted ≡ hi base
  ∧ region shifted ≡ region base
  ∧ writeable shifted ≡ writeable base

stateMetadataEq :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
stateMetadataEq current original =
  dataLengthEq current original
  ∧ off current ≡ off original
  ∧ lo current ≡ lo original
  ∧ hi current ≡ hi original
  ∧ writeable current ≡ writeable original
  ∧ region current ≡ region original

storeShape :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
storeShape written alias before =
  dataEq written alias
  ∧ dataLengthEq alias before
  ∧ off written ≡ off before
  ∧ lo written ≡ lo before
  ∧ hi written ≡ hi before
  ∧ writeable written ≡ writeable before
  ∧ region written ≡ region before

segmentUnchanged :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Set
segmentUnchanged current original i size =
  (j : Int) →
  (signed32 i ≤Z j ∧ j <Z signed32 size) →
  pelts current (addInt (off current) j)
    ≡ pelts original (addInt (off current) j)

outsideUnchanged :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Set
outsideUnchanged current original size =
  (j : Int) →
  (j <Z off current ∨
   addInt (off current) (signed32 size) ≤Z j) →
  pelts current j ≡ pelts original j

carryBounds : Word64 → Set
carryBounds carry =
  zeroZ ≤Z unsignedZ carry
  ∧ unsignedZ carry ≤Z oneZ

zeroFlag : Word64 → Bool → Set
zeroFlag limb flag =
  (unsignedZ limb ≡ unsignedZ zero64 → flag ≡ true)
  ∧ (flag ≡ true → limb ≡ zero64)

initialInvariant :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Ptr Zone Word64 →
  Set
initialInvariant original size shifted =
  (zeroZ ≤Z zeroZ ∧ zeroZ ≤Z signed32 size)
  ∧ Not (zero32 ≡ size)
  ∧ off shifted ≡ addInt (off original) zeroZ
  ∧ peltsEq shifted original
  ∧ plength shifted ≡ plength original
  ∧ (lo shifted ≡ lo original ∧ hi shifted ≡ hi original)
  ∧ Not (oneZ ≡ zeroZ)
  ∧ (zeroZ ≤Z oneZ ∧ oneZ ≤Z oneZ)
  ∧ writeable shifted ≡ true
  ∧ addInt
      (value original zeroZ)
      (multiplyInt (powerInt radixZ zeroZ) oneZ)
    ≡ addInt (value original zeroZ) oneZ

loopInvariant :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word64 →
  Ptr Zone Word64 →
  Set
loopInvariant original size cursor i carry result current =
  (zeroZ ≤Z signed32 i ∧ signed32 i ≤Z signed32 size)
  ∧ (i ≡ size → Not (unsignedZ result ≡ zeroZ))
  ∧ off cursor ≡ addInt (off current) (signed32 i)
  ∧ peltsEq cursor current
  ∧ plength cursor ≡ plength current
  ∧ (lo cursor ≡ lo current ∧ hi cursor ≡ hi current)
  ∧ Iff
      (Not (unsignedZ result ≡ zeroZ))
      (unsignedZ carry ≡ zeroZ)
  ∧ carryBounds carry
  ∧ writeable cursor ≡ true
  ∧ addInt
      (value current (signed32 i))
      (multiplyInt
        (powerInt radixZ (signed32 i))
        (unsignedZ carry))
    ≡ addInt (value original (signed32 i)) oneZ
  ∧ segmentUnchanged current original i size
  ∧ outsideUnchanged current original size

nextLoopInvariant :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Set
nextLoopInvariant original size previous-i result current next-i carry cursor =
  (zeroZ ≤Z subtractInt (signed32 size) (signed32 previous-i)
   ∧ subtractInt (signed32 size) (signed32 next-i)
       <Z subtractInt (signed32 size) (signed32 previous-i))
  ∧ (zeroZ ≤Z signed32 next-i
     ∧ signed32 next-i ≤Z signed32 size)
  ∧ (next-i ≡ size → Not (unsignedZ result ≡ zeroZ))
  ∧ off cursor ≡ addInt (off current) (signed32 next-i)
  ∧ peltsEq cursor current
  ∧ plength cursor ≡ plength current
  ∧ (lo cursor ≡ lo current ∧ hi cursor ≡ hi current)
  ∧ Iff
      (Not (unsignedZ result ≡ zeroZ))
      (unsignedZ carry ≡ zeroZ)
  ∧ carryBounds carry
  ∧ writeable cursor ≡ true
  ∧ addInt
      (value current (signed32 next-i))
      (multiplyInt
        (powerInt radixZ (signed32 next-i))
        (unsignedZ carry))
    ≡ addInt (value original (signed32 next-i)) oneZ
  ∧ segmentUnchanged current original next-i size
  ∧ outsideUnchanged current original size

afterIndexIncrement :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word64 →
  Set
afterIndexIncrement original size before i result written current carry =
  int32InBounds (addInt (signed32 i) oneZ)
  ∧
  ((next-i : Word32) →
    signed32 next-i ≡ addInt (signed32 i) oneZ →
    (lo written ≤Z addInt (off written) oneZ
     ∧ addInt (off written) oneZ ≤Z hi written)
    ∧
    ((cursor : Ptr _ Word64) →
      fullPointerShift cursor written oneZ →
      nextLoopInvariant
        original size i result current next-i carry cursor))

afterMemoryUpdate :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Word64 →
  Set
afterMemoryUpdate original size before i result current carry =
  (written alias : Ptr _ Word64) →
  storeShape written alias before →
  storeShape written alias before →
  stateMetadataEq alias current →
  mapUpdatedAt written before (off written) result →
  afterIndexIncrement
    original size before i result written alias carry

storedResultBranch :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Word64 →
  Set
storedResultBranch original size cursor i result current carry =
  (accessAt cursor (off cursor)
   ∧ writeable cursor ≡ true)
  ∧ afterMemoryUpdate
      original size cursor i result current carry

afterIncrementResult :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Set
afterIncrementResult original size cursor i result current =
  (flag : Bool) →
  zeroFlag result flag →
  IfSet
    flag
    (storedResultBranch
      original size cursor i result current one64)
    (storedResultBranch
      original size cursor i result current zero64)

incrementStep :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Ptr Zone Word64 →
  Word32 →
  Ptr Zone Word64 →
  Set
incrementStep original size cursor i current =
  accessAt cursor (off cursor)
  ∧
  ((result : Word64) →
    unsignedZ result
      ≡ incrementModuloRadix (pelts cursor (off cursor)) →
    afterIncrementResult original size cursor i result current)

loopExit :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Ptr Zone Word64 →
  Set
loopExit original size current =
  value current (signed32 size)
    ≡ addInt (value original (signed32 size)) oneZ
  ∧ outsideUnchanged current original size

loopContinuation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Set
loopContinuation original size cursor i result current =
  (flag : Bool) →
  zeroFlag result flag →
  IfSet
    flag
    (incrementStep original size cursor i current)
    (loopExit original size current)

loopObligation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Set
loopObligation original size =
  (cursor : Ptr _ Word64) →
  (i : Word32) →
  (carry result : Word64) →
  (current : Ptr _ Word64) →
  stateMetadataEq current original →
  loopInvariant original size cursor i carry result current →
  loopContinuation original size cursor i result current

WmpnIncr1VC :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Set
WmpnIncr1VC original size =
  lo original ≤Z addInt (off original) zeroZ
  ∧ addInt (off original) zeroZ ≤Z hi original
  ∧
  ((shifted : Ptr _ Word64) →
    fullPointerShift shifted original zeroZ →
    initialInvariant original size shifted
    ∧ loopObligation original size)

wmpn-incr-1'vc : Set₁
wmpn-incr-1'vc =
  (Zone : Set) →
  (original : Ptr Zone Word64) →
  (size : Word32) →
  valid original (signed32 size) →
  zeroZ <Z signed32 size →
  addInt (value original (signed32 size)) oneZ
    <Z powerInt radixZ (signed32 size) →
  writeable original ≡ true →
  WmpnIncr1VC original size
