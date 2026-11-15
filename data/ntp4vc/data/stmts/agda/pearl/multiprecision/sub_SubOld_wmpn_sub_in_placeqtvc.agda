-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/sub_SubOld_wmpn_sub_in_placeqtvc: the verification
-- condition for in-place unequal-length multiprecision subtraction, including
-- borrow propagation, pointer validity, and frame preservation. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module SubSubOldWmpnSubInPlaceVC where

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
  Int →
  Word64 →
  Set
valueEquation current original y size y-size borrow =
  subtractInt
      (value current size)
      (multiplyInt
        (powerInt radixZ size)
        (unsignedZ borrow))
    ≡ subtractInt
        (value original size)
        (value y y-size)

zeroFlag : Word64 → Bool → Set
zeroFlag word flag =
  (unsignedZ word ≡ unsignedZ zero64 → flag ≡ true)
  ∧ (flag ≡ true → word ≡ zero64)

AfterIncrement :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Bool →
  Set
AfterIncrement sy sx x y i b x3 next-i old-limb flag =
  IfSet
    (notBool flag)
    (valueEquation
        x3 x y (signed32 sx) (signed32 sy) zero64
     ∧ borrowBounds zero64
     ∧ unchangedOutside x3 x (signed32 sx))
    ((zeroZ ≤Z subtractInt (signed32 sx) (signed32 i)
      ∧ subtractInt (signed32 sx) (signed32 next-i)
          <Z subtractInt (signed32 sx) (signed32 i))
     ∧ (signed32 sy ≤Z signed32 next-i
        ∧ signed32 next-i ≤Z signed32 sx)
     ∧ valueEquation
          x3 x y (signed32 next-i) (signed32 sy) b
     ∧ borrowBounds b
     ∧ (next-i ≡ sx ∨ unsignedZ b ≡ oneZ)
     ∧ tailEqual
          x3 x (signed32 next-i) (signed32 sx)
     ∧ unchangedOutside x3 x (signed32 sx))

AfterWrite :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Word64 →
  Set
AfterWrite sy sx x y i b x3 old-limb =
  int32InBounds (addInt (signed32 i) oneZ)
  ∧
  ((next-i : Word32) →
    signed32 next-i ≡ addInt (signed32 i) oneZ →
    (flag : Bool) →
    zeroFlag old-limb flag →
    AfterIncrement sy sx x y i b x3 next-i old-limb flag)

WriteStep :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Set
WriteStep sy sx x y i b x2 =
  accessAt x2 (addInt (off x2) (signed32 i))
  ∧
  ((result : Word64) →
    unsignedZ result ≡
      decrementModuloRadix
        (pelts x2 (addInt (off x2) (signed32 i))) →
    (accessAt x2 (addInt (off x2) (signed32 i))
     ∧ writeable x2 ≡ true)
    ∧
    ((x3 : Ptr _ Word64) →
      sameShape x3 x2 →
      (mapUpdatedAt
         x3
         x2
         (addInt (off x3) (signed32 i))
         result
       ∧ pelts x3 (addInt (off x3) (signed32 i))
           ≡ result) →
      AfterWrite
        sy sx x y i b x3
        (pelts x2 (addInt (off x2) (signed32 i)))))

loopInvariant :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Set
loopInvariant sy sx x y i b x2 =
  (signed32 sy ≤Z signed32 i
   ∧ signed32 i ≤Z signed32 sx)
  ∧ valueEquation x2 x y (signed32 i) (signed32 sy) b
  ∧ borrowBounds b
  ∧ (i ≡ sx ∨ unsignedZ b ≡ oneZ)
  ∧ tailEqual x2 x (signed32 i) (signed32 sx)
  ∧ unchangedOutside x2 x (signed32 sx)

finishedWithBorrow :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word64 →
  Ptr Zone Word64 →
  Set
finishedWithBorrow sy sx x y b x2 =
  valueEquation x2 x y (signed32 sx) (signed32 sy) b
  ∧ borrowBounds b
  ∧ unchangedOutside x2 x (signed32 sx)

LoopStep :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Set
LoopStep sy sx x y i b x2 =
  IfSet
    (intLess (signed32 i) (signed32 sx))
    (WriteStep sy sx x y i b x2)
    (finishedWithBorrow sy sx x y b x2)

BorrowLoop :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
BorrowLoop sy sx x y x1 =
  (i : Word32) →
  (b : Word64) →
  (x2 : Ptr _ Word64) →
  sameShape x2 x1 →
  loopInvariant sy sx x y i b x2 →
  LoopStep sy sx x y i b x2

continueAfterY :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word64 →
  Set
continueAfterY sy sx x y x1 borrow =
  ((signed32 sy ≤Z signed32 sy
    ∧ signed32 sy ≤Z signed32 sx)
   ∧ valueEquation
        x1 x y (signed32 sy) (signed32 sy) borrow
   ∧ borrowBounds borrow
   ∧ (sy ≡ sx ∨ unsignedZ borrow ≡ oneZ)
   ∧ tailEqual x1 x (signed32 sy) (signed32 sx)
   ∧ unchangedOutside x1 x (signed32 sx))
  ∧ BorrowLoop sy sx x y x1

finishAfterY :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word64 →
  Set
finishAfterY sy sx x y x1 borrow =
  valueEquation x1 x y (signed32 sx) (signed32 sy) borrow
  ∧ borrowBounds borrow
  ∧ unchangedOutside x1 x (signed32 sx)

AfterYFlag :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word64 →
  Bool →
  Set
AfterYFlag sy sx x y x1 borrow flag =
  IfSet
    (notBool flag)
    (continueAfterY sy sx x y x1 borrow)
    (finishAfterY sy sx x y x1 borrow)

AfterY :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word64 →
  Set
AfterY sy sx x y x1 borrow =
  (flag : Bool) →
  zeroFlag borrow flag →
  AfterYFlag sy sx x y x1 borrow flag

InitialBorrow :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word64 →
  Set
InitialBorrow sy sx x y x1 borrow =
  (borrowBounds borrow
   ∧ valueEquation
        x1 x y (signed32 sy) (signed32 sy) borrow
   ∧ unchangedOutside x1 x (signed32 sy)) →
  AfterY sy sx x y x1 borrow

AfterInitialSubtraction :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
AfterInitialSubtraction sy sx x y x1 =
  (borrow : Word64) →
  InitialBorrow sy sx x y x1 borrow

AllInitialStates :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
AllInitialStates sy sx x y =
  (x1 : Ptr _ Word64) →
  sameShape x1 x →
  AfterInitialSubtraction sy sx x y x1

WmpnSubInPlaceVC :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
WmpnSubInPlaceVC sy sx x y =
  zeroZ ≤Z signed32 sy
  ∧ valid x (signed32 sy)
  ∧ valid y (signed32 sy)
  ∧ writeable x ≡ true
  ∧ AllInitialStates sy sx x y

wmpn-sub-in-place'vc : Set₁
wmpn-sub-in-place'vc =
  (Zone : Set) →
  (sy sx : Word32) →
  (x y : Ptr Zone Word64) →
  zeroZ ≤Z signed32 sy →
  signed32 sy ≤Z signed32 sx →
  valid x (signed32 sx) →
  valid y (signed32 sy) →
  writeable x ≡ true →
  WmpnSubInPlaceVC sy sx x y
