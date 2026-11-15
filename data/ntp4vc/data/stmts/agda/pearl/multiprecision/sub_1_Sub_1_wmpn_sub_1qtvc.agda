-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/sub_1_Sub_1_wmpn_sub_1qtvc: the weakest-precondition
-- verification condition for subtracting one 64-bit limb from a positive-length
-- multiprecision input into a separate output, including borrow propagation,
-- copying of remaining limbs, and memory framing. This file contains no proof.

{-# OPTIONS --safe #-}

module SubOneSubOneWmpnSubOneVC where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
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
notBool false = true
notBool true = false

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
  []V  : Vec A zero
  _∷V_ : {n : Nat} → A → Vec A n → Vec A (suc n)

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

valid : {Zone : Set} → Ptr Zone Word64 → Int → Set
valid p size =
  int32InBounds size
  ∧ zeroZ ≤Z size
  ∧ (zeroZ ≤Z lo p ∧ lo p ≤Z off p)
  ∧ addInt (off p) size ≤Z hi p
  ∧ hi p ≤Z plength p

sameMetadata :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
sameMetadata newer older =
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

unchangedOutside :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Int →
  Set
unchangedOutside current original-output size =
  (j : Int) →
  (j <Z off current ∨
   addInt (off current) size ≤Z j) →
  pelts current j ≡ pelts original-output j

borrowBounds : Word64 → Set
borrowBounds borrow =
  zeroZ ≤Z unsignedZ borrow
  ∧ unsignedZ borrow ≤Z oneZ

zeroFlag : Word64 → Bool → Set
zeroFlag limb flag =
  (unsignedZ limb ≡ unsignedZ zero64 → flag ≡ true)
  ∧ (flag ≡ true → limb ≡ zero64)

CopyInvariant :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word32 →
  Word64 →
  Set
CopyInvariant current input original-output index borrow size subtrahend =
  (index ≡ size ∨ unsignedZ borrow ≡ zeroZ)
  ∧ (zeroZ ≤Z signed32 index
     ∧ signed32 index ≤Z signed32 size)
  ∧ subtractInt
      (value current (signed32 index))
      (multiplyInt
        (powerInt radixZ (signed32 index))
        (unsignedZ borrow))
    ≡ subtractInt
        (value input (signed32 index))
        (unsignedZ subtrahend)
  ∧ unchangedOutside current original-output (signed32 size)

CopyFinalState :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word64 →
  Set
CopyFinalState current input original-output size subtrahend borrow =
  subtractInt
      (value current (signed32 size))
      (multiplyInt
        (powerInt radixZ (signed32 size))
        (unsignedZ borrow))
    ≡ subtractInt
        (value input (signed32 size))
        (unsignedZ subtrahend)
  ∧ unchangedOutside current original-output (signed32 size)
  ∧ borrowBounds borrow

CopyNextIndex :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word32 →
  Word64 →
  Set
CopyNextIndex current input original-output index borrow size subtrahend =
  (next-index : Word32) →
  signed32 next-index ≡ addInt (signed32 index) oneZ →
  (zeroZ ≤Z subtractInt (signed32 size) (signed32 index)
   ∧ subtractInt (signed32 size) (signed32 next-index)
       <Z subtractInt (signed32 size) (signed32 index))
  ∧ CopyInvariant
      current input original-output next-index borrow size subtrahend

CopyWriteContinuation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word32 →
  Word64 →
  Set
CopyWriteContinuation
  current input original-output index borrow size subtrahend =
  (newer : Ptr _ Word64) →
  sameMetadata newer current →
  (mapUpdatedAt
      newer
      current
      (addInt (off newer) (signed32 index))
      (pelts input (addInt (off input) (signed32 index)))
   ∧ pelts newer (addInt (off newer) (signed32 index))
       ≡ pelts input (addInt (off input) (signed32 index))) →
  int32InBounds (addInt (signed32 index) oneZ)
  ∧ CopyNextIndex
      newer input original-output index borrow size subtrahend

CopyStateContinuation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word32 →
  Word64 →
  Set
CopyStateContinuation
  current input original-output index borrow size subtrahend =
  IfSet
    (intLess (signed32 index) (signed32 size))
    (accessAt input (addInt (off input) (signed32 index))
     ∧ (accessAt current (addInt (off current) (signed32 index))
        ∧ writeable current ≡ true)
     ∧ CopyWriteContinuation
         current input original-output index borrow size subtrahend)
    (CopyFinalState
      current input original-output size subtrahend borrow)

CopyLoopStates :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word64 →
  Set
CopyLoopStates initial-memory input original-output size subtrahend borrow =
  (index : Word32) →
  (current : Ptr _ Word64) →
  sameMetadata current initial-memory →
  CopyInvariant
    current input original-output index borrow size subtrahend →
  CopyStateContinuation
    current input original-output index borrow size subtrahend

CopyPackage :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word32 →
  Word64 →
  Set
CopyPackage current input original-output index borrow size subtrahend =
  CopyInvariant
    current input original-output index borrow size subtrahend
  ∧ CopyLoopStates
      current input original-output size subtrahend borrow

BorrowInvariant :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word32 →
  Word64 →
  Set
BorrowInvariant current input original-output index borrow size subtrahend =
  (oneZ ≤Z signed32 index
   ∧ signed32 index ≤Z signed32 size)
  ∧ borrowBounds borrow
  ∧ (index ≡ size ∨ unsignedZ borrow ≡ oneZ)
  ∧ subtractInt
      (value current (signed32 index))
      (multiplyInt
        (powerInt radixZ (signed32 index))
        (unsignedZ borrow))
    ≡ subtractInt
        (value input (signed32 index))
        (unsignedZ subtrahend)
  ∧ unchangedOutside current original-output (signed32 size)

BorrowZeroTestContinuation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word64 →
  Word32 →
  Word64 →
  Word64 →
  Set
BorrowZeroTestContinuation
  current input original-output index next-index borrow size subtrahend
  old-input-limb =
  (flag : Bool) →
  zeroFlag old-input-limb flag →
  IfSet
    (notBool flag)
    (CopyPackage
      current input original-output next-index zero64 size subtrahend)
    ((zeroZ ≤Z subtractInt (signed32 size) (signed32 index)
      ∧ subtractInt (signed32 size) (signed32 next-index)
          <Z subtractInt (signed32 size) (signed32 index))
     ∧ BorrowInvariant
          current input original-output
          next-index borrow size subtrahend)

BorrowNextIndexContinuation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word32 →
  Word64 →
  Word64 →
  Set
BorrowNextIndexContinuation
  current input original-output index borrow size subtrahend old-input-limb =
  (next-index : Word32) →
  signed32 next-index ≡ addInt (signed32 index) oneZ →
  BorrowZeroTestContinuation
    current input original-output index next-index borrow size subtrahend
    old-input-limb

BorrowWriteContinuation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word32 →
  Word64 →
  Word64 →
  Word64 →
  Set
BorrowWriteContinuation
  current input original-output index borrow size subtrahend
  old-input-limb result =
  (newer : Ptr _ Word64) →
  sameMetadata newer current →
  (mapUpdatedAt
      newer
      current
      (addInt (off newer) (signed32 index))
      result
   ∧ pelts newer (addInt (off newer) (signed32 index)) ≡ result) →
  int32InBounds (addInt (signed32 index) oneZ)
  ∧ BorrowNextIndexContinuation
      newer input original-output index borrow size subtrahend old-input-limb

BorrowResultContinuation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word32 →
  Word64 →
  Word64 →
  Set
BorrowResultContinuation
  current input original-output index borrow size subtrahend old-input-limb =
  (result : Word64) →
  unsignedZ result ≡ decrementModuloRadix old-input-limb →
  (accessAt current (addInt (off current) (signed32 index))
   ∧ writeable current ≡ true)
  ∧ BorrowWriteContinuation
      current input original-output index borrow size subtrahend
      old-input-limb result

BorrowStateContinuation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word32 →
  Word64 →
  Set
BorrowStateContinuation
  current input original-output index borrow size subtrahend =
  IfSet
    (intLess (signed32 index) (signed32 size))
    (accessAt input (addInt (off input) (signed32 index))
     ∧ BorrowResultContinuation
         current input original-output index borrow size subtrahend
         (pelts input (addInt (off input) (signed32 index))))
    (CopyPackage
      current input original-output index borrow size subtrahend)

BorrowLoopStates :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Set
BorrowLoopStates after-first input original-output size subtrahend =
  (index : Word32) →
  (borrow : Word64) →
  (current : Ptr _ Word64) →
  sameMetadata current after-first →
  BorrowInvariant
    current input original-output index borrow size subtrahend →
  BorrowStateContinuation
    current input original-output index borrow size subtrahend

InitialBorrowPackage :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Set
InitialBorrowPackage after-first input original-output size subtrahend =
  BorrowInvariant
    after-first input original-output one32 one64 size subtrahend
  ∧ BorrowLoopStates
      after-first input original-output size subtrahend

AfterFirstWrite :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word64 →
  Set
AfterFirstWrite after-first input original-output size subtrahend first-limb =
  IfSet
    (natLess (unsignedNat first-limb) (unsignedNat subtrahend))
    (InitialBorrowPackage
      after-first input original-output size subtrahend)
    (CopyPackage
      after-first input original-output one32 zero64 size subtrahend)

FirstWriteContinuation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word64 →
  Word64 →
  Set
FirstWriteContinuation
  input original-output size subtrahend first-limb result =
  (after-first : Ptr _ Word64) →
  sameMetadata after-first original-output →
  mapUpdatedAt after-first original-output (off after-first) result →
  AfterFirstWrite
    after-first input original-output size subtrahend first-limb

FirstResultContinuation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word64 →
  Set
FirstResultContinuation input original-output size subtrahend first-limb =
  (result : Word64) →
  unsignedZ result ≡ subtractModuloRadix first-limb subtrahend →
  (accessAt original-output (off original-output)
   ∧ writeable original-output ≡ true)
  ∧ FirstWriteContinuation
      input original-output size subtrahend first-limb result

WmpnSubOneVC :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Ptr Zone Word64 →
  Word64 →
  Set
WmpnSubOneVC input size original-output subtrahend =
  accessAt input (off input)
  ∧
  (let first-limb = pelts input (off input)
   in
   FirstResultContinuation
     input original-output size subtrahend first-limb)

wmpn-sub-1'vc : Set₁
wmpn-sub-1'vc =
  (Zone : Set) →
  (input : Ptr Zone Word64) →
  (size : Word32) →
  (original-output : Ptr Zone Word64) →
  (subtrahend : Word64) →
  valid input (signed32 size) →
  valid original-output (signed32 size) →
  zeroZ <Z signed32 size →
  writeable original-output ≡ true →
  WmpnSubOneVC input size original-output subtrahend
