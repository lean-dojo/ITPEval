-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/add_1_Add_1_wmpn_add_1_in_placeqtvc: the weakest
-- precondition for in-place addition of one 64-bit limb to a positive-length
-- multiprecision integer, including carry propagation. This file contains no proof.

{-# OPTIONS --safe #-}

module AddOneAddOneWmpnAddOneInPlaceVC where

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

zero64 one64 : Word64
zero64 = natToVec 64 0
one64 = natToVec 64 1

one32 : Word32
one32 = natToVec 32 1

radixNat : Nat
radixNat = 18446744073709551616

modRadix : Nat → Nat
modRadix n with natLess n radixNat
... | true = n
... | false = subtractNat n radixNat

addModuloRadix : Word64 → Word64 → Int
addModuloRadix x y =
  pos (modRadix (unsignedNat x + unsignedNat y))

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

accessAt :
  {Zone : Set} →
  Ptr Zone Word64 →
  Int →
  Set
accessAt p index =
  lo p ≤Z index ∧ index <Z hi p

carryBounds : Word64 → Set
carryBounds carry =
  zeroZ ≤Z unsignedZ carry
  ∧ unsignedZ carry ≤Z oneZ

LoopInvariant :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word32 →
  Word64 →
  Set
LoopInvariant original current i carry size addend =
  (oneZ ≤Z signed32 i ∧ signed32 i ≤Z signed32 size)
  ∧ carryBounds carry
  ∧ (unsignedZ carry ≡ oneZ ∨ i ≡ size)
  ∧ addInt
      (value current (signed32 i))
      (multiplyInt
        (powerInt radixZ (signed32 i))
        (unsignedZ carry))
    ≡ addInt
        (value original (signed32 i))
        (unsignedZ addend)
  ∧ unchangedOutside current original (signed32 i)

FinishedWithCarry :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word64 →
  Set
FinishedWithCarry original current size carry addend =
  addInt
      (value current (signed32 size))
      (multiplyInt
        (powerInt radixZ (signed32 size))
        (unsignedZ carry))
    ≡ addInt
        (value original (signed32 size))
        (unsignedZ addend)
  ∧ carryBounds carry
  ∧ unchangedOutside current original (signed32 size)

InitialNoCarry :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Set
InitialNoCarry original current size addend =
  addInt
      (value current (signed32 size))
      (multiplyInt
        (powerInt radixZ (signed32 size))
        zeroZ)
    ≡ addInt
        (value original (signed32 size))
        (unsignedZ addend)
  ∧ (zeroZ ≤Z zeroZ ∧ zeroZ ≤Z oneZ)
  ∧ unchangedOutside current original (signed32 size)

AfterIncrement :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word32 →
  Word64 →
  Word32 →
  Bool →
  Set
AfterIncrement original current size addend i carry next-i flag =
  IfSet
    (notBool flag)
    (addInt
        (value current (signed32 size))
        (multiplyInt
          (powerInt radixZ (signed32 size))
          (unsignedZ zero64))
      ≡ addInt
          (value original (signed32 size))
          (unsignedZ addend)
     ∧ carryBounds zero64
     ∧ unchangedOutside current original (signed32 size))
    ((zeroZ ≤Z subtractInt (signed32 size) (signed32 i)
      ∧ subtractInt (signed32 size) (signed32 next-i)
          <Z subtractInt (signed32 size) (signed32 i))
     ∧ (oneZ ≤Z signed32 next-i
        ∧ signed32 next-i ≤Z signed32 size)
     ∧ carryBounds carry
     ∧ (unsignedZ carry ≡ oneZ ∨ next-i ≡ size)
     ∧ addInt
          (value current (signed32 next-i))
          (multiplyInt
            (powerInt radixZ (signed32 next-i))
            (unsignedZ carry))
        ≡ addInt
            (value original (signed32 next-i))
            (unsignedZ addend)
     ∧ unchangedOutside current original (signed32 next-i))

AfterWrite :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word32 →
  Word64 →
  Word64 →
  Set
AfterWrite original current size addend i carry result =
  int32InBounds (addInt (signed32 i) oneZ)
  ∧
  ((next-i : Word32) →
    signed32 next-i ≡ addInt (signed32 i) oneZ →
    (flag : Bool) →
    ((unsignedZ result ≡ unsignedZ zero64 → flag ≡ true)
     ∧ (flag ≡ true → result ≡ zero64)) →
    AfterIncrement
      original current size addend i carry next-i flag)

WriteStep :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word32 →
  Word64 →
  Set
WriteStep original current size addend i carry =
  accessAt current (addInt (off current) (signed32 i))
  ∧
  ((result : Word64) →
    unsignedZ result ≡
      incrementModuloRadix
        (pelts current (addInt (off current) (signed32 i))) →
    (accessAt current (addInt (off current) (signed32 i))
     ∧ writeable current ≡ true)
    ∧
    ((newer : Ptr _ Word64) →
      sameShape newer current →
      (mapUpdatedAt
         newer
         current
         (addInt (off newer) (signed32 i))
         result
       ∧ pelts newer (addInt (off newer) (signed32 i))
           ≡ result) →
      AfterWrite original newer size addend i carry result))

LoopStep :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word32 →
  Word64 →
  Set
LoopStep original current size addend i carry =
  IfSet
    (intLess (signed32 i) (signed32 size))
    (WriteStep original current size addend i carry)
    (FinishedWithCarry original current size carry addend)

CarryLoop :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Set
CarryLoop original after-first size addend =
  (i : Word32) →
  (carry : Word64) →
  (current : Ptr _ Word64) →
  sameShape current after-first →
  LoopInvariant original current i carry size addend →
  LoopStep original current size addend i carry

InitialCarryInvariant :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Set
InitialCarryInvariant original after-first size addend =
  ((oneZ ≤Z oneZ ∧ oneZ ≤Z signed32 size)
   ∧ carryBounds one64
   ∧ (unsignedZ one64 ≡ oneZ ∨ one32 ≡ size)
   ∧ addInt
        (value after-first oneZ)
        (multiplyInt
          (powerInt radixZ oneZ)
          (unsignedZ one64))
      ≡ addInt
          (value original oneZ)
          (unsignedZ addend)
   ∧ unchangedOutside after-first original oneZ)
  ∧ CarryLoop original after-first size addend

AfterFirstWrite :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word64 →
  Word64 →
  Set
AfterFirstWrite original after-first size addend old-limb result =
  IfSet
    (natLess (unsignedNat result) (unsignedNat old-limb))
    (InitialCarryInvariant original after-first size addend)
    (InitialNoCarry original after-first size addend)

FirstResult :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word64 →
  Word64 →
  Set
FirstResult original size addend old-limb result =
  (accessAt original (off original)
   ∧ writeable original ≡ true)
  ∧
  ((after-first : Ptr _ Word64) →
    sameShape after-first original →
    mapUpdatedAt
      after-first
      original
      (off after-first)
      result →
    AfterFirstWrite
      original after-first size addend old-limb result)

WmpnAdd1InPlaceVC :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Set
WmpnAdd1InPlaceVC original size addend =
  accessAt original (off original)
  ∧
  (let old-limb = pelts original (off original)
   in
   (result : Word64) →
   unsignedZ result ≡ addModuloRadix old-limb addend →
   FirstResult original size addend old-limb result)

wmpn-add-1-in-place'vc : Set₁
wmpn-add-1-in-place'vc =
  (Zone : Set) →
  (original : Ptr Zone Word64) →
  (size : Word32) →
  (addend : Word64) →
  valid original (signed32 size) →
  zeroZ <Z signed32 size →
  writeable original ≡ true →
  WmpnAdd1InPlaceVC original size addend
