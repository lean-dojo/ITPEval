-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/sub_1_Sub_1_wmpn_decrqtvc: the weakest-precondition
-- verification condition for subtracting one 64-bit limb from a nonempty
-- multiprecision value in place, including borrow propagation, pointer
-- updates, and memory framing. This file contains no proof.

{-# OPTIONS --safe #-}

module SubOneSubOneWmpnDecrVC where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; div-helper)

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

notBool : Bool → Bool
notBool true = false
notBool false = true

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
  negative (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc _) = zero

natDivide : Nat → Nat → Nat
natDivide n zero = zero
natDivide n (suc m) = div-helper zero m n m

natModulo : Nat → Nat → Nat
natModulo n zero = zero
natModulo n d@(suc _) =
  n - d * natDivide n d

euclideanModuloPositive : Int → Nat → Int
euclideanModuloPositive _ zero = pos zero
euclideanModuloPositive (pos n) d@(suc _) =
  pos (natModulo n d)
euclideanModuloPositive (negsuc n) d@(suc _) with natModulo (suc n) d
... | zero = pos zero
... | r@(suc _) = pos (d - r)

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

radixNat : Nat
radixNat = 18446744073709551616

int32InBounds : Int → Set
int32InBounds n =
  min32 ≤Z n ∧ n ≤Z max32

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

one32 : Word32
one32 = natToVec 32 1

zero64 one64 : Word64
zero64 = natToVec 64 0
one64 = natToVec 64 1

subtractModuloRadix : Word64 → Word64 → Int
subtractModuloRadix left-limb right-limb =
  euclideanModuloPositive
    (subtractInt (unsignedZ left-limb) (unsignedZ right-limb))
    radixNat

decrementModuloRadix : Word64 → Int
decrementModuloRadix limb =
  subtractModuloRadix limb one64

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

nthList : {A : Set} → A → Nat → List A → A
nthList default index [] = default
nthList default zero (x ∷ xs) = x
nthList default (suc index) (_ ∷ xs) =
  nthList default index xs

record Ptr (Zone A : Set) : Set where
  constructor pointer
  field
    contents  : List A
    off       : Int
    lo        : Int
    hi        : Int
    writeable : Bool
    region    : Zone

open Ptr public

pelts : {Zone : Set} → Ptr Zone Word64 → Int → Word64
pelts p index =
  nthList zero64 (intToNat index) (contents p)

plength : {Zone : Set} → Ptr Zone Word64 → Int
plength p = pos (listLength (contents p))

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
peltsEq p q =
  FunctionEq (pelts p) (pelts q)

dataEq :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
dataEq p q =
  contents p ≡ contents q

dataLengthEq :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
dataLengthEq p q =
  listLength (contents p) ≡ listLength (contents q)

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

loopPointer :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Int →
  Set
loopPointer cursor current index =
  off cursor ≡ addInt (off current) index
  ∧ peltsEq cursor current
  ∧ plength cursor ≡ plength current
  ∧ (lo cursor ≡ lo current ∧ hi cursor ≡ hi current)

segmentUnchanged :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Int →
  Word32 →
  Set
segmentUnchanged current original start size =
  (j : Int) →
  (start ≤Z j ∧ j <Z signed32 size) →
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

borrowBounds : Word64 → Set
borrowBounds borrow =
  zeroZ ≤Z unsignedZ borrow
  ∧ unsignedZ borrow ≤Z oneZ

zeroFlag : Word64 → Bool → Set
zeroFlag limb flag =
  (unsignedZ limb ≡ unsignedZ zero64 → flag ≡ true)
  ∧ (flag ≡ true → limb ≡ zero64)

finalState :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Set
finalState original size addend current =
  value current (signed32 size)
    ≡ subtractInt
        (value original (signed32 size))
        (unsignedZ addend)
  ∧ outsideUnchanged current original size

initialLoopInvariant :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
initialLoopInvariant original size addend cursor current =
  (oneZ ≤Z oneZ ∧ oneZ ≤Z signed32 size)
  ∧ loopPointer cursor current oneZ
  ∧ (one32 ≡ size → unsignedZ one64 ≡ zeroZ)
  ∧ borrowBounds one64
  ∧ writeable cursor ≡ true
  ∧ subtractInt
      (value current oneZ)
      (multiplyInt
        (powerInt radixZ oneZ)
        (unsignedZ one64))
    ≡ subtractInt
        (value original oneZ)
        (unsignedZ addend)
  ∧ segmentUnchanged current original oneZ size
  ∧ outsideUnchanged current original size

loopInvariant :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Set
loopInvariant original size addend cursor index carry current =
  (oneZ ≤Z signed32 index
   ∧ signed32 index ≤Z signed32 size)
  ∧ loopPointer cursor current (signed32 index)
  ∧ (index ≡ size → unsignedZ carry ≡ zeroZ)
  ∧ borrowBounds carry
  ∧ writeable cursor ≡ true
  ∧ subtractInt
      (value current (signed32 index))
      (multiplyInt
        (powerInt radixZ (signed32 index))
        (unsignedZ carry))
    ≡ subtractInt
        (value original (signed32 index))
        (unsignedZ addend)
  ∧ segmentUnchanged current original (signed32 index) size
  ∧ outsideUnchanged current original size

nextLoopInvariant :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word32 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
nextLoopInvariant
  original size addend previous-index next-index carry cursor current =
  (zeroZ ≤Z
      subtractInt (signed32 size) (signed32 previous-index)
   ∧ subtractInt (signed32 size) (signed32 next-index)
       <Z subtractInt (signed32 size) (signed32 previous-index))
  ∧ loopInvariant
      original size addend cursor next-index carry current

afterIndexIncrement :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word32 →
  Word64 →
  Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
afterIndexIncrement
  original size addend index carry old-limb written current =
  int32InBounds (addInt (signed32 index) oneZ)
  ∧
  ((next-index : Word32) →
    signed32 next-index ≡ addInt (signed32 index) oneZ →
    (lo written ≤Z addInt (off written) oneZ
     ∧ addInt (off written) oneZ ≤Z hi written)
    ∧
    ((cursor : Ptr _ Word64) →
      fullPointerShift cursor written oneZ →
      (flag : Bool) →
      zeroFlag old-limb flag →
      IfSet
        (notBool flag)
        (finalState original size addend current)
        (nextLoopInvariant
          original size addend index next-index carry cursor current)))

secondWriteContinuation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word64 →
  Ptr Zone Word64 →
  Set
secondWriteContinuation
  original size addend before index carry result current =
  (written alias : Ptr _ Word64) →
  storeShape written alias before →
  storeShape written alias before →
  stateMetadataEq alias current →
  mapUpdatedAt written before (off written) result →
  afterIndexIncrement
    original size addend index carry
    (pelts before (off before)) written alias

secondResultContinuation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Set
secondResultContinuation
  original size addend cursor index carry current =
  accessAt cursor (off cursor)
  ∧
  ((result : Word64) →
    unsignedZ result ≡
      decrementModuloRadix (pelts cursor (off cursor)) →
    (accessAt cursor (off cursor)
     ∧ writeable cursor ≡ true)
    ∧ secondWriteContinuation
        original size addend cursor index carry result current)

loopContinuation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Set
loopContinuation
  original size addend cursor index carry current =
  (flag : Bool) →
  zeroFlag carry flag →
  IfSet
    (notBool flag)
    (secondResultContinuation
      original size addend cursor index carry current)
    (finalState original size addend current)

loopObligation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Set
loopObligation original size addend initial-memory =
  (index : Word32) →
  (cursor : Ptr _ Word64) →
  (carry : Word64) →
  (current : Ptr _ Word64) →
  stateMetadataEq current initial-memory →
  loopInvariant
    original size addend cursor index carry current →
  loopContinuation
    original size addend cursor index carry current

borrowBranch :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
borrowBranch original size addend cursor current =
  initialLoopInvariant
    original size addend cursor current
  ∧ loopObligation original size addend current

firstWriteContinuation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word64 →
  Word64 →
  Ptr Zone Word64 →
  Set
firstWriteContinuation
  original size addend initial-limb result shifted =
  (cursor current : Ptr _ Word64) →
  storeShape cursor current shifted →
  stateMetadataEq current original →
  mapUpdatedAt current original (off current) result →
  IfSet
    (intLess (unsignedZ initial-limb) (unsignedZ result))
    (borrowBranch original size addend cursor current)
    (finalState original size addend current)

firstResultContinuation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word64 →
  Ptr Zone Word64 →
  Set
firstResultContinuation original size addend initial-limb shifted =
  (result : Word64) →
  unsignedZ result ≡
    subtractModuloRadix initial-limb addend →
  (accessAt original (off original)
   ∧ writeable original ≡ true)
  ∧ firstWriteContinuation
      original size addend initial-limb result shifted

shiftContinuation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word64 →
  Set
shiftContinuation original size addend initial-limb =
  (shifted : Ptr _ Word64) →
  fullPointerShift shifted original oneZ →
  firstResultContinuation
    original size addend initial-limb shifted

WmpnDecrVC :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Set
WmpnDecrVC original size addend =
  lo original ≤Z off original
  ∧ off original <Z hi original
  ∧
  ((lo original ≤Z addInt (off original) oneZ
    ∧ addInt (off original) oneZ ≤Z hi original)
   ∧ shiftContinuation
       original size addend (pelts original (off original)))

wmpn-decr'vc : Set₁
wmpn-decr'vc =
  (Zone : Set) →
  (original : Ptr Zone Word64) →
  (size : Word32) →
  (addend : Word64) →
  valid original (signed32 size) →
  zeroZ <Z signed32 size →
  zeroZ ≤Z
    subtractInt
      (value original (signed32 size))
      (unsignedZ addend) →
  writeable original ≡ true →
  WmpnDecrVC original size addend
