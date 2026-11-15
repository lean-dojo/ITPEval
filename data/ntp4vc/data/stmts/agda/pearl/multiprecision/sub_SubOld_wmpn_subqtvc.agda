-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/sub_SubOld_wmpn_subqtvc: the verification condition
-- for unequal-length multiprecision subtraction into a separate result
-- pointer, including borrow propagation, limb copying, pointer updates, and
-- frame preservation. This file contains no proof.

{-# OPTIONS --safe #-}

module sub_SubOld_wmpn_subqtvc where

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

zero64 : Word64
zero64 = natToVec 64 0

radixNat : Nat
radixNat = 18446744073709551616

decrementModuloRadix : Word64 → Int
decrementModuloRadix limb with unsignedNat limb
... | zero = pos (subtractNat radixNat 1)
... | suc n = pos n

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

outsideUnchanged :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Int →
  Set
outsideUnchanged current original size =
  (j : Int) →
  (j <Z off current ∨
   addInt (off current) size ≤Z j) →
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
  Int →
  Word64 →
  Set
valueEquation current x y size y-size borrow =
  subtractInt
      (value current size)
      (multiplyInt
        (powerInt radixZ size)
        (unsignedZ borrow))
    ≡ subtractInt
        (value x size)
        (value y y-size)

decreases :
  Word32 →
  Word32 →
  Word32 →
  Set
decreases size current next =
  zeroZ ≤Z subtractInt (signed32 size) (signed32 current)
  ∧ subtractInt (signed32 size) (signed32 next)
      <Z subtractInt (signed32 size) (signed32 current)

copyNextInvariant :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Set
copyNextInvariant current originalR x y sy sx i next-i borrow =
  decreases sx i next-i
  ∧ (signed32 sy ≤Z signed32 next-i
     ∧ signed32 next-i ≤Z signed32 sx)
  ∧ (next-i ≡ sx ∨ unsignedZ borrow ≡ zeroZ)
  ∧ valueEquation
      current x y (signed32 next-i) (signed32 sy) borrow
  ∧ outsideUnchanged current originalR (signed32 sx)

copyAfterWrite :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Set
copyAfterWrite current originalR x y sy sx i borrow =
  int32InBounds (addInt (signed32 i) oneZ)
  ∧
  ((next-i : Word32) →
    signed32 next-i ≡ addInt (signed32 i) oneZ →
    copyNextInvariant
      current originalR x y sy sx i next-i borrow)

copyUpdatedStep :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Set
copyUpdatedStep before originalR x y sy sx i borrow =
  (after : Ptr _ Word64) →
  sameShape after before →
  (mapUpdatedAt
     after
     before
     (addInt (off after) (signed32 i))
     (pelts x (addInt (off x) (signed32 i)))
   ∧ pelts after (addInt (off after) (signed32 i))
       ≡ pelts x (addInt (off x) (signed32 i))) →
  copyAfterWrite after originalR x y sy sx i borrow

copyLoopInvariant :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Set
copyLoopInvariant current originalR x y sy sx i borrow =
  (signed32 sy ≤Z signed32 i
   ∧ signed32 i ≤Z signed32 sx)
  ∧ (i ≡ sx ∨ unsignedZ borrow ≡ zeroZ)
  ∧ valueEquation current x y (signed32 i) (signed32 sy) borrow
  ∧ outsideUnchanged current originalR (signed32 sx)

copyFinished :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word64 →
  Set
copyFinished current originalR x y sy sx borrow =
  valueEquation current x y (signed32 sx) (signed32 sy) borrow
  ∧ outsideUnchanged current originalR (signed32 sx)
  ∧ borrowBounds borrow

copyLoopStep :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Set
copyLoopStep current originalR x y sy sx i borrow =
  IfSet
    (intLess (signed32 i) (signed32 sx))
    (accessAt x (addInt (off x) (signed32 i))
     ∧ (accessAt current (addInt (off current) (signed32 i))
        ∧ writeable current ≡ true)
     ∧ copyUpdatedStep current originalR x y sy sx i borrow)
    (copyFinished current originalR x y sy sx borrow)

allCopyLoopStates :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word64 →
  Set
allCopyLoopStates base originalR x y sy sx borrow =
  (i : Word32) →
  (current : Ptr _ Word64) →
  sameShape current base →
  copyLoopInvariant current originalR x y sy sx i borrow →
  copyLoopStep current originalR x y sy sx i borrow

zeroFlag : Word64 → Bool → Set
zeroFlag word flag =
  (unsignedZ word ≡ unsignedZ zero64 → flag ≡ true)
  ∧ (flag ≡ true → word ≡ zero64)

borrowAfterIncrement :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Word32 →
  Bool →
  Set
borrowAfterIncrement current originalR x y sy sx i borrow next-i flag =
  IfSet
    (notBool flag)
    (copyLoopInvariant
       current originalR x y sy sx next-i zero64
     ∧ allCopyLoopStates
         current originalR x y sy sx zero64)
    (decreases sx i next-i
     ∧ (signed32 sy ≤Z signed32 next-i
        ∧ signed32 next-i ≤Z signed32 sx)
     ∧ valueEquation
         current x y (signed32 next-i) (signed32 sy) borrow
     ∧ outsideUnchanged current originalR (signed32 sx)
     ∧ borrowBounds borrow
     ∧ (next-i ≡ sx ∨ unsignedZ borrow ≡ oneZ))

borrowAfterWrite :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Word64 →
  Set
borrowAfterWrite current originalR x y sy sx i borrow old-limb =
  int32InBounds (addInt (signed32 i) oneZ)
  ∧
  ((next-i : Word32) →
    signed32 next-i ≡ addInt (signed32 i) oneZ →
    (flag : Bool) →
    zeroFlag old-limb flag →
    borrowAfterIncrement
      current originalR x y sy sx i borrow next-i flag)

borrowUpdatedStep :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Word64 →
  Set
borrowUpdatedStep before originalR x y sy sx i borrow result =
  (after : Ptr _ Word64) →
  sameShape after before →
  (mapUpdatedAt
     after
     before
     (addInt (off after) (signed32 i))
     result
   ∧ pelts after (addInt (off after) (signed32 i))
       ≡ result) →
  borrowAfterWrite
    after originalR x y sy sx i borrow
    (pelts x (addInt (off x) (signed32 i)))

borrowResultStep :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Set
borrowResultStep current originalR x y sy sx i borrow =
  (result : Word64) →
  unsignedZ result ≡
    decrementModuloRadix
      (pelts x (addInt (off x) (signed32 i))) →
  (accessAt current (addInt (off current) (signed32 i))
   ∧ writeable current ≡ true)
  ∧ borrowUpdatedStep
      current originalR x y sy sx i borrow result

borrowLoopInvariant :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Set
borrowLoopInvariant current originalR x y sy sx i borrow =
  (signed32 sy ≤Z signed32 i
   ∧ signed32 i ≤Z signed32 sx)
  ∧ valueEquation current x y (signed32 i) (signed32 sy) borrow
  ∧ outsideUnchanged current originalR (signed32 sx)
  ∧ borrowBounds borrow
  ∧ (i ≡ sx ∨ unsignedZ borrow ≡ oneZ)

borrowFinished :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word64 →
  Set
borrowFinished current originalR x y sy sx borrow =
  valueEquation current x y (signed32 sx) (signed32 sy) borrow
  ∧ outsideUnchanged current originalR (signed32 sx)
  ∧ borrowBounds borrow

borrowLoopStep :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Set
borrowLoopStep current originalR x y sy sx i borrow =
  IfSet
    (intLess (signed32 i) (signed32 sx))
    (accessAt x (addInt (off x) (signed32 i))
     ∧ borrowResultStep current originalR x y sy sx i borrow)
    (copyLoopInvariant current originalR x y sy sx i borrow
     ∧ allCopyLoopStates current originalR x y sy sx borrow)

allBorrowLoopStates :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Set
allBorrowLoopStates base originalR x y sy sx =
  (i : Word32) →
  (borrow : Word64) →
  (current : Ptr _ Word64) →
  sameShape current base →
  borrowLoopInvariant current originalR x y sy sx i borrow →
  borrowLoopStep current originalR x y sy sx i borrow

initialNonzeroBranch :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word64 →
  Set
initialNonzeroBranch firstR originalR x y sy sx borrow =
  borrowLoopInvariant firstR originalR x y sy sx sy borrow
  ∧ allBorrowLoopStates firstR originalR x y sy sx

initialZeroBranch :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word64 →
  Set
initialZeroBranch firstR originalR x y sy sx borrow =
  copyLoopInvariant firstR originalR x y sy sx sy borrow
  ∧ allCopyLoopStates firstR originalR x y sy sx borrow

afterInitialFlag :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word64 →
  Bool →
  Set
afterInitialFlag firstR originalR x y sy sx borrow flag =
  IfSet
    (notBool flag)
    (initialNonzeroBranch firstR originalR x y sy sx borrow)
    (initialZeroBranch firstR originalR x y sy sx borrow)

afterInitialBorrow :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word64 →
  Set
afterInitialBorrow firstR originalR x y sy sx borrow =
  (flag : Bool) →
  zeroFlag borrow flag →
  afterInitialFlag firstR originalR x y sy sx borrow flag

initialBorrow :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word64 →
  Set
initialBorrow firstR originalR x y sy sx borrow =
  (borrowBounds borrow
   ∧ valueEquation
       firstR x y (signed32 sy) (signed32 sy) borrow
   ∧ outsideUnchanged firstR originalR (signed32 sy)) →
  afterInitialBorrow firstR originalR x y sy sx borrow

allInitialBorrows :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Set
allInitialBorrows firstR originalR x y sy sx =
  (borrow : Word64) →
  initialBorrow firstR originalR x y sy sx borrow

allFirstResults :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Set
allFirstResults originalR x y sy sx =
  (firstR : Ptr _ Word64) →
  sameShape firstR originalR →
  allInitialBorrows firstR originalR x y sy sx

wmpn-sub'vc : Set₁
wmpn-sub'vc =
  (Zone : Set) →
  (sy sx : Word32) →
  (x y result : Ptr Zone Word64) →
  zeroZ ≤Z signed32 sy →
  signed32 sy ≤Z signed32 sx →
  valid x (signed32 sx) →
  valid y (signed32 sy) →
  valid result (signed32 sx) →
  writeable result ≡ true →
  valid x (signed32 sy)
  ∧ valid y (signed32 sy)
  ∧ valid result (signed32 sy)
  ∧ writeable result ≡ true
  ∧ allFirstResults result x y sy sx
