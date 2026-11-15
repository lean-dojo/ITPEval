-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/get_str_Get_str_wmpn_get_str_bitsqtvc: the verification
-- condition for extracting base-2^bits digits from a multiprecision integer,
-- including fixed-width conversions, loop invariants, pointer updates, frame
-- preservation, and the final string-value postcondition. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module get_str_Get_str_wmpn_get_str_bitsqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; div-helper)

infix 4 _≤Z_ _<Z_ _≠_
infixr 5 _∷V_
infixr 3 _∧_
infixr 2 _∨_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

_≠_ : {A : Set} → A → A → Set
x ≠ y = Not (x ≡ y)

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

IfInt : Bool → Int → Int → Int
IfInt true when-true when-false = when-true
IfInt false when-true when-false = when-false

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
multiplyInt (pos m) (negsuc n) = negative (m * suc n)
multiplyInt (negsuc m) (pos n) = negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) = pos (suc m * suc n)

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc _) = zero

absoluteNat : Int → Nat
absoluteNat (pos n) = n
absoluteNat (negsuc n) = suc n

powerNat : Int → Nat → Int
powerNat base zero = pos 1
powerNat base (suc exponent) =
  multiplyInt base (powerNat base exponent)

powerInt : Int → Int → Int
powerInt base exponent = powerNat base (intToNat exponent)

natDivide : Nat → Nat → Nat
natDivide n zero = zero
natDivide n (suc m) = div-helper zero m n m

natModulo : Nat → Nat → Nat
natModulo n zero = zero
natModulo n d@(suc _) = n - d * natDivide n d

computerDivide : Int → Int → Int
computerDivide _ (pos zero) = pos zero
computerDivide _ (negsuc _) = pos zero
computerDivide (pos n) (pos (suc m)) =
  pos (natDivide n (suc m))
computerDivide (negsuc n) (pos (suc m)) =
  negative (natDivide (suc n) (suc m))

computerModulo : Int → Int → Int
computerModulo dividend divisor =
  subtractInt dividend
    (multiplyInt divisor (computerDivide dividend divisor))

euclideanModuloPositive : Int → Nat → Int
euclideanModuloPositive _ zero = pos zero
euclideanModuloPositive (pos n) d@(suc _) = pos (natModulo n d)
euclideanModuloPositive (negsuc n) d@(suc _) with natModulo (suc n) d
... | zero = pos zero
... | r@(suc _) = pos (d - r)

euclideanModulo : Int → Int → Int
euclideanModulo dividend divisor =
  euclideanModuloPositive dividend (absoluteNat divisor)

euclideanDivide : Int → Int → Int
euclideanDivide dividend divisor =
  computerDivide
    (subtractInt dividend (euclideanModulo dividend divisor))
    divisor

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

Word8 Word32 Word64 : Set
Word8 = Vec Bool 8
Word32 = Vec Bool 32
Word64 = Vec Bool 64

signed8 : Word8 → Int
signed8 bits with lastBit bits
... | false = unsignedZ bits
... | true = subtractInt (unsignedZ bits) (pos 256)

signed32 : Word32 → Int
signed32 bits with lastBit bits
... | false = unsignedZ bits
... | true = subtractInt (unsignedZ bits) (pos 4294967296)

zero32 : Word32
zero32 = natToVec 32 0

one64 : Word64
one64 = natToVec 64 1

zeroZ oneZ twoZ sevenZ eightZ sixtyFourZ max8Z max32Z radixZ max64Z : Int
zeroZ = pos 0
oneZ = pos 1
twoZ = pos 2
sevenZ = pos 7
eightZ = pos 8
sixtyFourZ = pos 64
max8Z = pos 255
max32Z = pos 2147483647
radixZ = pos 18446744073709551616
max64Z = pos 18446744073709551615

min32Z : Int
min32Z = negsuc 2147483647

int32InBounds : Int → Set
int32InBounds value =
  min32Z ≤Z value ∧ value ≤Z max32Z

uint64InBounds : Int → Set
uint64InBounds value =
  zeroZ ≤Z value ∧ value ≤Z max64Z

FunctionEqual :
  {A B : Set} → (A → B) → (A → B) → Set
FunctionEqual f g = (x : _) → f x ≡ g x

update :
  {A : Set} → (Int → A) → Int → A → Int → A
update f index value query with intEqual query index
... | true = value
... | false = f query

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

pelts :
  {Zone A : Set} → Ptr Zone A → Int → A
pelts p = memory p

plength :
  {Zone A : Set} → Ptr Zone A → Int
plength p = pos (cellCount p)

valid :
  {Zone A : Set} → Ptr Zone A → Int → Set
valid p size =
  int32InBounds size
  ∧ zeroZ ≤Z size
  ∧ (zeroZ ≤Z lo p ∧ lo p ≤Z off p)
  ∧ addInt (off p) size ≤Z hi p
  ∧ hi p ≤Z plength p

accessAt :
  {Zone A : Set} → Ptr Zone A → Int → Set
accessAt p index =
  lo p ≤Z index ∧ index <Z hi p

sameFrame :
  {Zone A : Set} → Ptr Zone A → Ptr Zone A → Set
sameFrame newer older =
  cellCount newer ≡ cellCount older
  ∧ off newer ≡ off older
  ∧ lo newer ≡ lo older
  ∧ hi newer ≡ hi older
  ∧ writeable newer ≡ writeable older
  ∧ region newer ≡ region older

valueMapFrom : (Int → Word64) → Int → Nat → Int
valueMapFrom limbs index zero = zeroZ
valueMapFrom limbs index (suc count) =
  addInt
    (unsignedZ (limbs index))
    (multiplyInt
      radixZ
      (valueMapFrom limbs (addInt index oneZ) count))

valueSub : (Int → Word64) → Int → Int → Int
valueSub limbs lower upper =
  valueMapFrom limbs lower
    (intToNat (subtractInt upper lower))

value :
  {Zone : Set} → Ptr Zone Word64 → Int → Int
value p size =
  valueSub (pelts p) (off p) (addInt (off p) size)

svalueMapFrom : Int → (Int → Word8) → Int → Nat → Int
svalueMapFrom base digits index zero = zeroZ
svalueMapFrom base digits index (suc count) =
  addInt
    (unsignedZ
      (digits
        (addInt index (pos count))))
    (multiplyInt
      base
      (svalueMapFrom base digits index count))

svalueSub : Int → (Int → Word8) → Int → Int → Int
svalueSub base digits lower upper =
  svalueMapFrom base digits lower
    (intToNat (subtractInt upper lower))

svalue :
  {Zone : Set} → Int → Ptr Zone Word8 → Int → Int
svalue base p size =
  svalueSub base (pelts p) (off p) (addInt (off p) size)

valueB :
  {Zone : Set} → Ptr Zone Word64 → Int → Int
valueB p bit-count =
  let limb-index = computerDivide bit-count sixtyFourZ
      low-bits = subtractInt bit-count
        (multiplyInt sixtyFourZ limb-index)
      partial =
        euclideanModulo
          (unsignedZ
            (pelts p (addInt (off p) limb-index)))
          (powerInt twoZ low-bits)
  in
  IfInt
    (intLess bit-count zeroZ)
    zeroZ
    (addInt
      (value p limb-index)
      (multiplyInt
        (powerInt radixZ limb-index)
        partial))

inBase :
  Int → (Int → Word8) → Int → Int → Set
inBase base digits lower upper =
  (index : Int) →
  (lower ≤Z index ∧ index <Z upper) →
  zeroZ ≤Z unsignedZ (digits index)
  ∧ unsignedZ (digits index) <Z base

outsideUnchanged :
  {Zone : Set} →
  Ptr Zone Word8 → Ptr Zone Word8 → Int → Set
outsideUnchanged current original end-index =
  (index : Int) →
  (index <Z off current
   ∨ addInt (off current) end-index ≤Z index) →
  pelts current index ≡ pelts original index

LoopInvariant :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word8 →
  Word32 → Word32 → Word32 → Word64 →
  Word64 → Word32 → Word32 → Ptr Zone Word8 → Set
LoopInvariant up original-sp bits un sn base shift j i current-sp =
  (zeroZ ≤Z signed32 i ∧ signed32 i ≤Z signed32 un)
  ∧ (zeroZ ≤Z signed32 j ∧ signed32 j ≤Z signed32 sn)
  ∧ (zeroZ <Z signed32 j →
      multiplyInt
        (subtractInt (signed32 sn) (signed32 j))
        (unsignedZ bits)
      ≡ addInt
          (multiplyInt sixtyFourZ (signed32 i))
          (unsignedZ shift))
  ∧ ((zeroZ ≤Z unsignedZ shift
      ∧ unsignedZ shift <Z sixtyFourZ)
     ∨ i ≡ un)
  ∧ inBase
      (unsignedZ base)
      (pelts current-sp)
      (addInt (off current-sp) (signed32 j))
      (addInt (off current-sp) (signed32 sn))
  ∧
    ((svalueSub
        (unsignedZ base)
        (pelts current-sp)
        (addInt (off current-sp) (signed32 j))
        (addInt (off current-sp) (signed32 sn))
      ≡ valueB up
          (multiplyInt
            (subtractInt (signed32 sn) (signed32 j))
            (unsignedZ bits))
      ∧ multiplyInt
          (subtractInt (signed32 sn) (signed32 j))
          (unsignedZ bits)
        ≤Z multiplyInt sixtyFourZ (signed32 un))
     ∨
     (signed32 j ≡ zeroZ
      ∧ svalue
          (unsignedZ base)
          current-sp
          (signed32 sn)
        ≡ value up (signed32 un)))
  ∧ outsideUnchanged current-sp original-sp (signed32 sn)

StorePostcondition :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word8 →
  Word32 → Word32 → Word32 → Word64 →
  Word32 → Word32 → Word32 → Word64 →
  Ptr Zone Word8 → Set
StorePostcondition
  up original-sp bits un sn base
  old-j new-j next-i next-shift stored-sp =
  signed32 new-j <Z signed32 old-j
  ∧ (zeroZ ≤Z signed32 next-i
     ∧ signed32 next-i ≤Z signed32 un)
  ∧ (zeroZ ≤Z signed32 new-j
     ∧ signed32 new-j ≤Z signed32 sn)
  ∧ multiplyInt
      (subtractInt (signed32 sn) (signed32 new-j))
      (unsignedZ bits)
    ≡ addInt
        (multiplyInt
          (subtractInt (signed32 sn) (signed32 old-j))
          (unsignedZ bits))
        (unsignedZ bits)
  ∧
    (zeroZ <Z signed32 new-j →
      addInt
        (multiplyInt
          (subtractInt (signed32 sn) (signed32 old-j))
          (unsignedZ bits))
        (unsignedZ bits)
      ≡ addInt
          (multiplyInt sixtyFourZ (signed32 next-i))
          (unsignedZ next-shift))
  ∧ ((zeroZ ≤Z unsignedZ next-shift
      ∧ unsignedZ next-shift <Z sixtyFourZ)
     ∨ next-i ≡ un)
  ∧ inBase
      (unsignedZ base)
      (pelts stored-sp)
      (addInt (off stored-sp) (signed32 new-j))
      (addInt (off stored-sp) (signed32 sn))
  ∧
    ((svalueSub
        (unsignedZ base)
        (pelts stored-sp)
        (addInt (off stored-sp) (signed32 new-j))
        (addInt (off stored-sp) (signed32 sn))
      ≡ valueB up
          (addInt
            (multiplyInt
              (subtractInt (signed32 sn) (signed32 old-j))
              (unsignedZ bits))
            (unsignedZ bits))
      ∧ addInt
          (multiplyInt
            (subtractInt (signed32 sn) (signed32 old-j))
            (unsignedZ bits))
          (unsignedZ bits)
        ≤Z multiplyInt sixtyFourZ (signed32 un))
     ∨
     (signed32 new-j ≡ zeroZ
      ∧ svalue
          (unsignedZ base)
          stored-sp
          (signed32 sn)
        ≡ value up (signed32 un)))
  ∧ outsideUnchanged stored-sp original-sp (signed32 sn)

WriteByte :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word8 → Ptr Zone Word8 →
  Word32 → Word32 → Word32 → Word64 →
  Word32 → Word32 → Word32 → Word64 → Word8 → Set
WriteByte
  {Zone} up original-sp current-sp bits un sn base
  old-j new-j next-i next-shift byte =
  (accessAt current-sp
      (addInt (off current-sp) (signed32 new-j))
   ∧ writeable current-sp ≡ true)
  ∧
  ((stored-sp : Ptr Zone Word8) →
    sameFrame stored-sp current-sp →
    (FunctionEqual
       (pelts stored-sp)
       (update
         (pelts current-sp)
         (addInt (off stored-sp) (signed32 new-j))
         byte)
     ∧ pelts stored-sp
          (addInt (off stored-sp) (signed32 new-j))
        ≡ byte) →
    StorePostcondition
      up original-sp bits un sn base
      old-j new-j next-i next-shift stored-sp)

StoreRemainder :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word8 → Ptr Zone Word8 →
  Word32 → Word32 → Word32 → Word64 →
  Word32 → Word32 → Word32 → Word64 → Int → Set
StoreRemainder
  up original-sp current-sp bits un sn base
  old-j new-j next-i next-shift remainder =
  (zeroZ ≤Z remainder ∧ remainder ≤Z max8Z)
  ∧
  ((byte : Word8) →
    unsignedZ byte ≡ remainder →
    WriteByte
      up original-sp current-sp bits un sn base
      old-j new-j next-i next-shift byte)

ComputerRemainderBranch :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word8 → Ptr Zone Word8 →
  Word32 → Word32 → Word32 → Word64 →
  Word32 → Word32 → Word32 → Word64 → Int → Set
ComputerRemainderBranch
  up original-sp current-sp bits un sn base
  old-j new-j next-i next-shift dividend =
  unsignedZ base ≠ zeroZ
  ∧ uint64InBounds
      (computerModulo dividend (unsignedZ base))
  ∧
  ((digit : Word64) →
    unsignedZ digit ≡
      computerModulo dividend (unsignedZ base) →
    StoreRemainder
      up original-sp current-sp bits un sn base
      old-j new-j next-i next-shift
      (unsignedZ digit))

WithHighLimb :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word8 → Ptr Zone Word8 →
  Word32 → Word32 → Word32 → Word64 →
  Word64 → Word32 → Word32 → Word32 → Word64 → Word64 → Set
WithHighLimb
  up original-sp current-sp bits un sn base
  low old-j new-j next-i next-shift high =
  uint64InBounds (addInt (unsignedZ low) (unsignedZ high))
  ∧
  ((combined : Word64) →
    unsignedZ combined ≡
      addInt (unsignedZ low) (unsignedZ high) →
    ComputerRemainderBranch
      up original-sp current-sp bits un sn base
      old-j new-j next-i next-shift
      (unsignedZ combined))

HighLimb :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word8 → Ptr Zone Word8 →
  Word32 → Word32 → Word32 → Word64 →
  Word64 → Word32 → Word32 → Word32 → Word64 → Set
HighLimb
  up original-sp current-sp bits un sn base
  low old-j new-j next-i amount-from-64 =
  accessAt up (addInt (off up) (signed32 next-i))
  ∧
  ((bits64 : Word64) →
    unsignedZ bits64 ≡ unsignedZ bits →
    uint64InBounds
      (subtractInt
        (unsignedZ bits64)
        (unsignedZ amount-from-64))
    ∧
    ((complement : Word64) →
      unsignedZ complement ≡
        subtractInt
          (unsignedZ bits64)
          (unsignedZ amount-from-64) →
      (zeroZ ≤Z unsignedZ complement
       ∧ unsignedZ complement <Z sixtyFourZ)
      ∧
      ((high : Word64) →
        unsignedZ high ≡
          euclideanModulo
            (multiplyInt
              (unsignedZ
                (pelts up
                  (addInt (off up) (signed32 next-i))))
              (powerInt twoZ (unsignedZ complement)))
            radixZ →
        WithHighLimb
          up original-sp current-sp bits un sn base
          low old-j new-j next-i amount-from-64 high)))

AfterCrossing64 :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word8 → Ptr Zone Word8 →
  Word32 → Word32 → Word32 → Word64 →
  Word64 → Word32 → Word32 → Word32 → Word64 → Set
AfterCrossing64
  up original-sp current-sp bits un sn base
  low old-j new-j current-i accumulated =
  int32InBounds (addInt (signed32 current-i) oneZ)
  ∧
  ((next-i : Word32) →
    signed32 next-i ≡
      addInt (signed32 current-i) oneZ →
    IfSet
      (intLess (signed32 next-i) (signed32 un))
      (uint64InBounds
        (subtractInt (unsignedZ accumulated) sixtyFourZ)
       ∧
       ((amount-from-64 : Word64) →
         unsignedZ amount-from-64 ≡
           subtractInt
             (unsignedZ accumulated)
             sixtyFourZ →
         HighLimb
           up original-sp current-sp bits un sn base
           low old-j new-j next-i amount-from-64))
      (ComputerRemainderBranch
        up original-sp current-sp bits un sn base
        old-j new-j next-i accumulated
        (unsignedZ low)))

AfterShiftAddition :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word8 → Ptr Zone Word8 →
  Word32 → Word32 → Word32 → Word64 →
  Word64 → Word64 → Word32 → Word32 → Word32 → Word64 → Set
AfterShiftAddition
  up original-sp current-sp bits un sn base
  low shift old-j new-j current-i bits64 =
  uint64InBounds
    (addInt (unsignedZ shift) (unsignedZ bits64))
  ∧
  ((accumulated : Word64) →
    unsignedZ accumulated ≡
      addInt (unsignedZ shift) (unsignedZ bits64) →
    IfSet
      (intLessOrEqual sixtyFourZ (unsignedZ accumulated))
      (AfterCrossing64
        up original-sp current-sp bits un sn base
        low old-j new-j current-i accumulated)
      (ComputerRemainderBranch
        up original-sp current-sp bits un sn base
        old-j new-j current-i accumulated
        (unsignedZ low)))

PositiveLoopBody :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word8 → Ptr Zone Word8 →
  Word32 → Word32 → Word32 → Word64 →
  Word64 → Word32 → Word32 → Set
PositiveLoopBody
  up original-sp current-sp bits un sn base shift j i =
  int32InBounds (subtractInt (signed32 j) oneZ)
  ∧
  ((new-j : Word32) →
    signed32 new-j ≡
      subtractInt (signed32 j) oneZ →
    accessAt up (addInt (off up) (signed32 i))
    ∧ (zeroZ ≤Z unsignedZ shift
       ∧ unsignedZ shift <Z sixtyFourZ)
    ∧
    ((low : Word64) →
      unsignedZ low ≡
        euclideanDivide
          (unsignedZ
            (pelts up (addInt (off up) (signed32 i))))
          (powerInt twoZ (unsignedZ shift)) →
      powerInt twoZ (unsignedZ shift) ≠ zeroZ
      ∧
      ((bits64 : Word64) →
        unsignedZ bits64 ≡ unsignedZ bits →
        AfterShiftAddition
          up original-sp current-sp bits un sn base
          low shift j new-j i bits64)))

ExitPostcondition :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word8 → Ptr Zone Word8 →
  Word32 → Word32 → Word32 → Word32 → Set
ExitPostcondition up original-sp current-sp bits un sn upper-bound =
  zeroZ ≤Z signed32 sn
  ∧
  ((result : Word32) →
    unsignedZ result ≡ signed32 sn →
    inBase
      (powerInt twoZ (unsignedZ bits))
      (pelts current-sp)
      (off current-sp)
      (addInt (off current-sp) (unsignedZ result))
    ∧ svalue
        (powerInt twoZ (unsignedZ bits))
        current-sp
        (unsignedZ result)
      ≡ value up (signed32 un)
    ∧ (zeroZ <Z unsignedZ result
       ∧ unsignedZ result ≤Z
          euclideanDivide
            (subtractInt
              (addInt
                (signed32 upper-bound)
                (unsignedZ bits))
              oneZ)
            (unsignedZ bits))
    ∧ zeroZ <Z
        unsignedZ (pelts current-sp (off current-sp))
    ∧
    ((index : Int) →
      (index <Z off current-sp
       ∨ addInt
           (off current-sp)
           (euclideanDivide
             (subtractInt
               (addInt
                 (signed32 upper-bound)
                 (unsignedZ bits))
               oneZ)
             (unsignedZ bits))
         ≤Z index) →
      pelts current-sp index ≡ pelts original-sp index))

LoopStep :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word8 →
  Word32 → Word32 → Word32 → Word32 → Word64 →
  Word64 → Word32 → Word32 → Ptr Zone Word8 → Set
LoopStep
  up original-sp bits un sn upper-bound base
  shift j i current-sp =
  IfSet
    (intLess zeroZ (signed32 j))
    (PositiveLoopBody
      up original-sp current-sp bits un sn base shift j i)
    (ExitPostcondition
      up original-sp current-sp bits un sn upper-bound)

AllLoopStates :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word8 →
  Word32 → Word32 → Word32 → Word32 → Word64 → Set
AllLoopStates
  {Zone} up original-sp bits un sn upper-bound base =
  (shift : Word64) →
  (j i : Word32) →
  (current-sp : Ptr Zone Word8) →
  sameFrame current-sp original-sp →
  LoopInvariant
    up original-sp bits un sn base
    shift j i current-sp →
  LoopStep
    up original-sp bits un sn upper-bound base
    shift j i current-sp

InitialState :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word8 →
  Word32 → Word32 → Word32 → Word32 → Word64 → Set
InitialState up sp bits un sn upper-bound base =
  (zeroZ ≤Z zeroZ ∧ zeroZ ≤Z signed32 un)
  ∧ (zeroZ ≤Z signed32 sn
     ∧ signed32 sn ≤Z signed32 sn)
  ∧ multiplyInt
      (subtractInt (signed32 sn) (signed32 sn))
      (unsignedZ bits)
    ≡ zeroZ
  ∧ (zeroZ <Z signed32 sn →
      zeroZ ≡ addInt
        (multiplyInt sixtyFourZ zeroZ)
        zeroZ)
  ∧ ((zeroZ ≤Z zeroZ ∧ zeroZ <Z sixtyFourZ)
     ∨ zero32 ≡ un)
  ∧ inBase
      (unsignedZ base)
      (pelts sp)
      (addInt (off sp) (signed32 sn))
      (addInt (off sp) (signed32 sn))
  ∧
    ((svalueSub
        (unsignedZ base)
        (pelts sp)
        (addInt (off sp) (signed32 sn))
        (addInt (off sp) (signed32 sn))
      ≡ valueB up zeroZ
      ∧ zeroZ ≤Z
          multiplyInt sixtyFourZ (signed32 un))
     ∨
     (signed32 sn ≡ zeroZ
      ∧ svalue
          (unsignedZ base)
          sp
          (signed32 sn)
        ≡ value up (signed32 un)))
  ∧ AllLoopStates up sp bits un sn upper-bound base

BaseConstruction :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word8 →
  Word32 → Word32 → Word32 → Word32 → Word64 → Set
BaseConstruction up sp bits un sn upper-bound bits64 =
  (base : Word64) →
  unsignedZ base ≡
    multiplyInt
      (powerInt twoZ (unsignedZ bits64))
      (unsignedZ one64) →
  InitialState up sp bits un sn upper-bound base

AfterDigitCount :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word8 →
  Word32 → Word32 → Word32 → Word32 → Set
AfterDigitCount up sp bits un upper-bound sn =
  (bits64 : Word64) →
  unsignedZ bits64 ≡ unsignedZ bits →
  ((zeroZ ≤Z unsignedZ bits64
    ∧ unsignedZ bits64 <Z sixtyFourZ)
   ∧ multiplyInt
        (powerInt twoZ (unsignedZ bits64))
        (unsignedZ one64)
      ≤Z max64Z)
  ∧ BaseConstruction up sp bits un sn upper-bound bits64

AfterTruncatedDivision :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word8 →
  Word32 → Word32 → Word32 → Word32 → Word32 → Set
AfterTruncatedDivision up sp bits un upper-bound exponent divisor =
  (sn : Word32) →
  signed32 sn ≡
    computerDivide
      (signed32 exponent)
      (signed32 divisor) →
  AfterDigitCount up sp bits un upper-bound sn

AfterExponent :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word8 →
  Word32 → Word32 → Word32 → Word32 → Set
AfterExponent up sp bits un upper-bound exponent =
  unsignedZ bits ≤Z max32Z
  ∧
  ((divisor : Word32) →
    signed32 divisor ≡ unsignedZ bits →
    (signed32 divisor ≠ zeroZ
     ∧ int32InBounds
        (computerDivide
          (signed32 exponent)
          (signed32 divisor)))
    ∧ AfterTruncatedDivision
        up sp bits un upper-bound exponent divisor)

AfterAccumulatedExponent :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word8 →
  Word32 → Word32 → Word32 → Word32 → Set
AfterAccumulatedExponent up sp bits un upper-bound accumulated =
  int32InBounds (subtractInt (signed32 accumulated) oneZ)
  ∧
  ((exponent : Word32) →
    signed32 exponent ≡
      subtractInt (signed32 accumulated) oneZ →
    AfterExponent up sp bits un upper-bound exponent)

ConversionChain :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word8 →
  Word32 → Word32 → Word32 → Word64 → Set
ConversionChain up sp bits un upper-bound bit-length =
  unsignedZ bits ≤Z max32Z
  ∧
  ((bits32 : Word32) →
    signed32 bits32 ≡ unsignedZ bits →
    unsignedZ bit-length ≤Z max32Z
    ∧
    ((bit-length32 : Word32) →
      signed32 bit-length32 ≡ unsignedZ bit-length →
      int32InBounds
        (subtractInt (signed32 un) oneZ)
      ∧
      ((last-index : Word32) →
        signed32 last-index ≡
          subtractInt (signed32 un) oneZ →
        int32InBounds
          (multiplyInt sixtyFourZ (signed32 last-index))
        ∧
        ((product : Word32) →
          signed32 product ≡
            multiplyInt sixtyFourZ (signed32 last-index) →
          int32InBounds
            (addInt
              (signed32 product)
              (signed32 bit-length32))
          ∧
          ((sum : Word32) →
            signed32 sum ≡
              addInt
                (signed32 product)
                (signed32 bit-length32) →
            int32InBounds
              (addInt (signed32 sum) (signed32 bits32))
            ∧
            ((accumulated : Word32) →
              signed32 accumulated ≡
                addInt (signed32 sum) (signed32 bits32) →
              AfterAccumulatedExponent
                up sp bits un upper-bound accumulated))))))

BitLengthObligation :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word8 →
  Word32 → Word32 → Word32 → Word64 → Set
BitLengthObligation
  up sp bits un upper-bound most-significant =
  (bit-length : Word64) →
  ((oneZ ≤Z unsignedZ bit-length
    ∧ unsignedZ bit-length ≤Z sixtyFourZ)
   ∧ powerInt
        twoZ
        (subtractInt (unsignedZ bit-length) oneZ)
      ≤Z unsignedZ most-significant
   ∧ unsignedZ most-significant
      <Z powerInt twoZ (unsignedZ bit-length)) →
  ConversionChain up sp bits un upper-bound bit-length

LastLimbObligation :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word8 →
  Word32 → Word32 → Word32 → Word32 → Set
LastLimbObligation up sp bits un upper-bound last-index =
  accessAt up (addInt (off up) (signed32 last-index))
  ∧
  let most-significant =
        pelts up (addInt (off up) (signed32 last-index))
  in
  zeroZ <Z unsignedZ most-significant
  ∧ BitLengthObligation
      up sp bits un upper-bound most-significant

MainConclusion :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word8 →
  Word32 → Word32 → Word32 → Set
MainConclusion up sp bits un upper-bound =
  int32InBounds
    (subtractInt (signed32 un) oneZ)
  ∧
  ((last-index : Word32) →
    signed32 last-index ≡
      subtractInt (signed32 un) oneZ →
    LastLimbObligation
      up sp bits un upper-bound last-index)

wmpn-get-str-bits'vc : Set₁
wmpn-get-str-bits'vc =
  (Zone : Set) →
  (un : Word32) →
  (up : Ptr Zone Word64) →
  (bits : Word32) →
  (sp : Ptr Zone Word8) →
  (ub : Word32) →
  oneZ ≤Z signed32 un →
  valid up (signed32 un) →
  oneZ ≤Z unsignedZ bits →
  unsignedZ bits ≤Z eightZ →
  valid sp
    (euclideanDivide
      (subtractInt
        (addInt (signed32 ub) (unsignedZ bits))
        oneZ)
      (unsignedZ bits)) →
  zeroZ ≤Z signed32 ub →
  value up (signed32 un)
    <Z powerInt twoZ (signed32 ub) →
  zeroZ <Z
    unsignedZ
      (pelts up
        (subtractInt
          (addInt (off up) (signed32 un))
          oneZ)) →
  addInt
      (multiplyInt sixtyFourZ (signed32 un))
      sevenZ
    ≤Z max32Z →
  writeable sp ≡ true →
  MainConclusion up sp bits un ub
