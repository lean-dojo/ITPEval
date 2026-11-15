-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/div_Div_div_qr_in_placeqtvc: the verification condition
-- for in-place multiprecision quotient-and-remainder division, including the
-- one-limb, two-limb, normalization, shifting, and quotient-padding branches.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module DivDivQrInPlaceVC where

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

zeroZ oneZ twoZ threeZ sixtyFourZ : Int
zeroZ = pos 0
oneZ = pos 1
twoZ = pos 2
threeZ = pos 3
sixtyFourZ = pos 64

min32 max32 radixZ halfRadixZ : Int
min32 = negsuc 2147483647
max32 = pos 2147483647
radixZ = pos 18446744073709551616
halfRadixZ = pos 9223372036854775808

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

zero32 one32 two32 : Word32
zero32 = natToVec 32 0
one32 = natToVec 32 1
two32 = natToVec 32 2

zero64 : Word64
zero64 = natToVec 64 0

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

valid :
  {Zone : Set} →
  Ptr Zone Word64 →
  Int →
  Set
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

accessAt :
  {Zone : Set} →
  Ptr Zone Word64 →
  Int →
  Set
accessAt p index =
  lo p ≤Z index ∧ index <Z hi p

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

updatedAtAndStored :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Int →
  Word64 →
  Set
updatedAtAndStored newer older index limb =
  mapUpdatedAt newer older index limb
  ∧ pelts newer index ≡ limb

mapEqSubShift :
  (Int → Word64) →
  (Int → Word64) →
  Int →
  Int →
  Int →
  Set
mapEqSubShift first second firstOffset secondOffset size =
  (i : Int) →
  (zeroZ ≤Z i ∧ i <Z size) →
  first (addInt firstOffset i) ≡ second (addInt secondOffset i)

outsideUnchanged :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Int →
  Set
outsideUnchanged current original size =
  (j : Int) →
  (j <Z off current ∨ addInt (off current) size ≤Z j) →
  pelts current j ≡ pelts original j

copiedRange :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Int →
  Set
copiedRange current source original size =
  mapEqSubShift
    (pelts current)
    (pelts source)
    (off current)
    (off source)
    size
  ∧ outsideUnchanged current original size

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

normalized :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Set
normalized p size =
  valid p (signed32 size)
  ∧ halfRadixZ ≤Z
      unsignedZ
        (pelts p
          (subtractInt
            (addInt (off p) (signed32 size))
            oneZ))

wordFlag :
  Word32 →
  Word32 →
  Bool →
  Set
wordFlag word constant flag =
  (signed32 word ≡ signed32 constant → flag ≡ true)
  ∧ (flag ≡ true → word ≡ constant)

shiftCountBounds : Word64 → Set
shiftCountBounds count =
  zeroZ <Z unsignedZ count
  ∧ unsignedZ count <Z sixtyFourZ

clzConditions : Word64 → Word32 → Set
clzConditions mostSignificant clz =
  multiplyInt
    (powerInt twoZ (signed32 clz))
    (unsignedZ mostSignificant)
    <Z radixZ
  ∧ radixZ ≤Z
      multiplyInt
        twoZ
        (multiplyInt
          (powerInt twoZ (signed32 clz))
          (unsignedZ mostSignificant))
  ∧ (zeroZ ≤Z signed32 clz ∧ signed32 clz <Z sixtyFourZ)
  ∧ multiplyInt
      (powerInt twoZ (signed32 clz))
      (unsignedZ mostSignificant)
      ≤Z
      subtractInt radixZ (powerInt twoZ (signed32 clz))

qrPost :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Set
qrPost originalX quotient divisor remainder sx sy =
  value originalX (signed32 sx)
    ≡ addInt
        (multiplyInt
          (value quotient
            (addInt
              (subtractInt (signed32 sx) (signed32 sy))
              oneZ))
          (value divisor (signed32 sy)))
        (value remainder (signed32 sy))
  ∧ value remainder (signed32 sy)
      <Z value divisor (signed32 sy)

divisionPremise :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Int →
  Int →
  Word64 →
  Set
divisionPremise dividend quotient divisor remainder totalSize divisorSize qh =
  value dividend totalSize
    ≡ addInt
        (multiplyInt
          (addInt
            (value quotient (subtractInt totalSize divisorSize))
            (multiplyInt
              (powerInt radixZ (subtractInt totalSize divisorSize))
              (unsignedZ qh)))
          (value divisor divisorSize))
        (value remainder divisorSize)
  ∧ value remainder divisorSize <Z value divisor divisorSize
  ∧ zeroZ ≤Z unsignedZ qh
  ∧ unsignedZ qh ≤Z oneZ

quotientPadding :
  {Zone : Set} →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word32 →
  Set
quotientPadding quotient sx sy adjust =
  (flag : Bool) →
  wordFlag adjust zero32 flag →
  IfSet
    flag
    (int32InBounds (subtractInt (signed32 sx) (signed32 sy))
     ∧
     ((index : Word32) →
       signed32 index ≡ subtractInt (signed32 sx) (signed32 sy) →
       (accessAt quotient (addInt (off quotient) (signed32 index))
        ∧ writeable quotient ≡ true)
       ∧
       ((padded : Ptr _ Word64) →
         sameShape padded quotient →
         updatedAtAndStored
           padded
           quotient
           (addInt (off padded) (signed32 index))
           zero64 →
         value padded
             (addInt
               (subtractInt (signed32 sx) (signed32 sy))
               oneZ)
           ≡ value quotient
               (addInt
                 (subtractInt (signed32 sx) (signed32 sy))
                 (signed32 adjust)))))
    (value quotient
        (addInt
          (subtractInt (signed32 sx) (signed32 sy))
          oneZ)
      ≡ value quotient
          (addInt
            (subtractInt (signed32 sx) (signed32 sy))
            (signed32 adjust)))

finishWithPadding :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word32 →
  Set
finishWithPadding originalX quotient divisor remainder sx sy adjust =
  quotientPadding quotient sx sy adjust
  ∧
  ((padded : Ptr _ Word64) →
    sameShape padded quotient →
    value padded
        (addInt
          (subtractInt (signed32 sx) (signed32 sy))
          oneZ)
      ≡ value quotient
          (addInt
            (subtractInt (signed32 sx) (signed32 sy))
            (signed32 adjust)) →
    qrPost originalX padded divisor remainder sx sy)

oneLimbBranch :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
oneLimbBranch sy sx x y q =
  accessAt y (off y)
  ∧
  (let divisor = pelts y (off y)
   in
   (valid x (signed32 sx)
    ∧ valid q (signed32 sx)
    ∧ writeable q ≡ true
    ∧ zeroZ <Z signed32 sx
    ∧ zeroZ <Z unsignedZ divisor)
   ∧
   ((q₁ : Ptr _ Word64) →
     sameShape q₁ q →
     (remainderLimb : Word64) →
     (value x (signed32 sx)
        ≡ addInt
            (multiplyInt
              (value q₁ (signed32 sx))
              (unsignedZ divisor))
            (unsignedZ remainderLimb)
      ∧ unsignedZ remainderLimb <Z unsignedZ divisor) →
     (accessAt x (off x) ∧ writeable x ≡ true)
     ∧
     ((x₁ : Ptr _ Word64) →
       sameShape x₁ x →
       mapUpdatedAt x₁ x (off x₁) remainderLimb →
       qrPost x q₁ y x₁ sx sy)))

div2Preconditions :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Set
div2Preconditions dividend divisor quotient total =
  twoZ ≤Z signed32 total
  ∧ valid dividend (signed32 total)
  ∧ valid divisor twoZ
  ∧ valid quotient (subtractInt (signed32 total) twoZ)
  ∧ halfRadixZ ≤Z
      unsignedZ (pelts divisor (addInt (off divisor) oneZ))
  ∧ writeable quotient ≡ true
  ∧ writeable dividend ≡ true

div2DirectContinuation :
  {Zone : Set} →
  Word32 →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
div2DirectContinuation sx sy total originalX divisor quotient dividend =
  (remainder q₁ : Ptr _ Word64) →
  sameShape remainder dividend →
  sameShape q₁ quotient →
  (qh : Word64) →
  divisionPremise
    dividend q₁ divisor remainder (signed32 total) twoZ qh →
  (valid remainder (signed32 sy)
   ∧ valid originalX (signed32 sy)
   ∧ writeable originalX ≡ true)
  ∧
  ((x₁ : Ptr _ Word64) →
    sameShape x₁ originalX →
    copiedRange x₁ remainder originalX (signed32 sy) →
    qrPost originalX q₁ divisor x₁ sx sy)

copyAppendZeroDiv2 :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
copyAppendZeroDiv2 sx sy originalX divisor quotient scratch =
  (copied : Ptr _ Word64) →
  sameShape copied scratch →
  copiedRange copied originalX scratch (signed32 sx) →
  (accessAt copied (addInt (off copied) (signed32 sx))
   ∧ writeable copied ≡ true)
  ∧
  ((extended : Ptr _ Word64) →
    sameShape extended copied →
    updatedAtAndStored
      extended
      copied
      (addInt (off extended) (signed32 sx))
      zero64 →
    int32InBounds (addInt (signed32 sx) oneZ)
    ∧
    ((total : Word32) →
      signed32 total ≡ addInt (signed32 sx) oneZ →
      div2Preconditions extended divisor quotient total
      ∧ div2DirectContinuation
          sx sy total originalX divisor quotient extended))

twoLimbUnshifted :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
twoLimbUnshifted sx sy x y q nx =
  (valid x (signed32 sx)
   ∧ valid nx (signed32 sx)
   ∧ writeable nx ≡ true)
  ∧ copyAppendZeroDiv2 sx sy x y q nx

twoLimbShiftedDivContinuation :
  {Zone : Set} →
  Word32 →
  Word32 →
  Word32 →
  Int →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Set
twoLimbShiftedDivContinuation sx sy clz scale
  originalX originalY q normalizedDivisor normalizedDividend total =
  div2Preconditions normalizedDividend normalizedDivisor q total
  ∧
  ((remainder q₁ : Ptr _ Word64) →
    sameShape remainder normalizedDividend →
    sameShape q₁ q →
    (qh : Word64) →
    divisionPremise
      normalizedDividend q₁ normalizedDivisor remainder
      (signed32 total) twoZ qh →
    zeroZ ≤Z signed32 clz
    ∧
    ((shift : Word64) →
      unsignedZ shift ≡ signed32 clz →
      (valid remainder (signed32 sy)
       ∧ valid originalX (signed32 sy)
       ∧ shiftCountBounds shift
       ∧ zeroZ <Z signed32 sy
       ∧ writeable originalX ≡ true)
      ∧
      ((restored : Ptr _ Word64) →
        sameShape restored originalX →
        (discarded : Word64) →
        addInt
            (unsignedZ discarded)
            (multiplyInt radixZ (value restored (signed32 sy)))
          ≡ multiplyInt
              (value remainder (signed32 sy))
              (powerInt
                twoZ
                (subtractInt sixtyFourZ (unsignedZ shift))) →
        value remainder twoZ
          ≡ multiplyInt scale (value restored twoZ)
        ∧
        (value remainder twoZ
            ≡ multiplyInt scale (value restored twoZ) →
          qrPost originalX q₁ originalY restored sx sy))))

twoLimbShifted :
  {Zone : Set} →
  Word32 →
  Word32 →
  Word32 →
  Int →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
twoLimbShifted sx sy clz scale x y q nx ny =
  zeroZ ≤Z signed32 clz
  ∧
  ((shiftY : Word64) →
    unsignedZ shiftY ≡ signed32 clz →
    (shiftCountBounds shiftY
     ∧ valid ny (signed32 sy)
     ∧ valid y (signed32 sy)
     ∧ writeable ny ≡ true
     ∧ zeroZ <Z signed32 sy)
    ∧
    ((normalizedY : Ptr _ Word64) →
      sameShape normalizedY ny →
      (carryY : Word64) →
      addInt
          (value normalizedY (signed32 sy))
          (multiplyInt
            (powerInt radixZ (signed32 sy))
            (unsignedZ carryY))
        ≡ multiplyInt
            (value y (signed32 sy))
            (powerInt twoZ (unsignedZ shiftY)) →
      (normalized normalizedY sy
       ∧ value normalizedY (signed32 sy)
           ≡ multiplyInt scale (value y (signed32 sy)))
      ∧
      ((normalized normalizedY sy
        ∧ value normalizedY (signed32 sy)
            ≡ multiplyInt scale (value y (signed32 sy))) →
        zeroZ ≤Z signed32 clz
        ∧
        ((shiftX : Word64) →
          unsignedZ shiftX ≡ signed32 clz →
          (shiftCountBounds shiftX
           ∧ valid nx (signed32 sx)
           ∧ valid x (signed32 sx)
           ∧ writeable nx ≡ true
           ∧ zeroZ <Z signed32 sx)
          ∧
          ((shiftedX : Ptr _ Word64) →
            sameShape shiftedX nx →
            (high : Word64) →
            addInt
                (value shiftedX (signed32 sx))
                (multiplyInt
                  (powerInt radixZ (signed32 sx))
                  (unsignedZ high))
              ≡ multiplyInt
                  (value x (signed32 sx))
                  (powerInt twoZ (unsignedZ shiftX)) →
            (accessAt shiftedX
               (addInt (off shiftedX) (signed32 sx))
             ∧ writeable shiftedX ≡ true)
            ∧
            ((extended : Ptr _ Word64) →
              sameShape extended shiftedX →
              updatedAtAndStored
                extended
                shiftedX
                (addInt (off extended) (signed32 sx))
                high →
              value extended (addInt (signed32 sx) oneZ)
                ≡ multiplyInt scale (value x (signed32 sx))
              ∧
              (value extended (addInt (signed32 sx) oneZ)
                  ≡ multiplyInt scale (value x (signed32 sx)) →
                int32InBounds (addInt (signed32 sx) oneZ)
                ∧
                ((total : Word32) →
                  signed32 total ≡ addInt (signed32 sx) oneZ →
                  twoLimbShiftedDivContinuation
                    sx sy clz scale x y q normalizedY
                    extended total))))))))

twoLimbCase :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
twoLimbCase sx sy x y q nx ny =
  int32InBounds (subtractInt (signed32 sy) oneZ)
  ∧
  ((topIndex : Word32) →
    signed32 topIndex ≡ subtractInt (signed32 sy) oneZ →
    accessAt y (addInt (off y) (signed32 topIndex))
    ∧
    (let mostSignificant =
           pelts y (addInt (off y) (signed32 topIndex))
     in
     zeroZ <Z unsignedZ mostSignificant
     ∧
     ((clz : Word32) →
       clzConditions mostSignificant clz →
       let scale = powerInt twoZ (signed32 clz)
       in
       (zeroFlag : Bool) →
       wordFlag clz zero32 zeroFlag →
       IfSet
         zeroFlag
         (twoLimbUnshifted sx sy x y q nx)
         (twoLimbShifted sx sy clz scale x y q nx ny))))

generalDivPreconditions :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
generalDivPreconditions sy total dividend divisor quotient =
  (threeZ ≤Z signed32 sy ∧ signed32 sy ≤Z signed32 total)
  ∧ valid dividend (signed32 total)
  ∧ valid divisor (signed32 sy)
  ∧ valid quotient (subtractInt (signed32 total) (signed32 sy))
  ∧ writeable quotient ≡ true
  ∧ writeable dividend ≡ true
  ∧ normalized divisor sy

generalDirectContinuation :
  {Zone : Set} →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
generalDirectContinuation sx sy adjust total x divisor q dividend =
  (remainder q₁ : Ptr _ Word64) →
  sameShape remainder dividend →
  sameShape q₁ q →
  (qh : Word64) →
  divisionPremise
    dividend q₁ divisor remainder
    (signed32 total) (signed32 sy) qh →
  (valid remainder (signed32 sy)
   ∧ valid x (signed32 sy)
   ∧ writeable x ≡ true)
  ∧
  ((restored : Ptr _ Word64) →
    sameShape restored x →
    copiedRange restored remainder x (signed32 sy) →
    finishWithPadding x q₁ divisor restored sx sy adjust)

generalUnshifted :
  {Zone : Set} →
  Word32 →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
generalUnshifted sx sy adjust x y q nx =
  (valid x (signed32 sx)
   ∧ valid nx (signed32 sx)
   ∧ writeable nx ≡ true)
  ∧
  ((copied : Ptr _ Word64) →
    sameShape copied nx →
    copiedRange copied x nx (signed32 sx) →
    (accessAt copied (addInt (off copied) (signed32 sx))
     ∧ writeable copied ≡ true)
    ∧
    ((extended : Ptr _ Word64) →
      sameShape extended copied →
      updatedAtAndStored
        extended copied
        (addInt (off extended) (signed32 sx))
        zero64 →
      int32InBounds (addInt (signed32 sx) (signed32 adjust))
      ∧
      ((total : Word32) →
        signed32 total
          ≡ addInt (signed32 sx) (signed32 adjust) →
        generalDivPreconditions sy total extended y q
        ∧ generalDirectContinuation
            sx sy adjust total x y q extended)))

generalShiftedContinuation :
  {Zone : Set} →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Int →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
generalShiftedContinuation sx sy adjust clz total scale
  x y q normalizedDividend normalizedDivisor =
  (remainder q₁ : Ptr _ Word64) →
  sameShape remainder normalizedDividend →
  sameShape q₁ q →
  (qh : Word64) →
  divisionPremise
    normalizedDividend q₁ normalizedDivisor remainder
    (signed32 total) (signed32 sy) qh →
  zeroZ ≤Z signed32 clz
  ∧
  ((shift : Word64) →
    unsignedZ shift ≡ signed32 clz →
    (valid remainder (signed32 sy)
     ∧ valid x (signed32 sy)
     ∧ shiftCountBounds shift
     ∧ zeroZ <Z signed32 sy
     ∧ writeable x ≡ true)
    ∧
    ((restored : Ptr _ Word64) →
      sameShape restored x →
      (discarded : Word64) →
      addInt
          (unsignedZ discarded)
          (multiplyInt radixZ (value restored (signed32 sy)))
        ≡ multiplyInt
            (value remainder (signed32 sy))
            (powerInt
              twoZ
              (subtractInt sixtyFourZ (unsignedZ shift))) →
      value remainder (signed32 sy)
        ≡ multiplyInt scale (value restored (signed32 sy))
      ∧
      (value remainder (signed32 sy)
          ≡ multiplyInt scale (value restored (signed32 sy)) →
        finishWithPadding x q₁ y restored sx sy adjust)))

generalShifted :
  {Zone : Set} →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Int →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
generalShifted sx sy adjust clz scale x y q nx ny =
  zeroZ ≤Z signed32 clz
  ∧
  ((shiftY : Word64) →
    unsignedZ shiftY ≡ signed32 clz →
    (shiftCountBounds shiftY
     ∧ valid ny (signed32 sy)
     ∧ valid y (signed32 sy)
     ∧ writeable ny ≡ true
     ∧ zeroZ <Z signed32 sy)
    ∧
    ((normalizedY : Ptr _ Word64) →
      sameShape normalizedY ny →
      (carryY : Word64) →
      addInt
          (value normalizedY (signed32 sy))
          (multiplyInt
            (powerInt radixZ (signed32 sy))
            (unsignedZ carryY))
        ≡ multiplyInt
            (value y (signed32 sy))
            (powerInt twoZ (unsignedZ shiftY)) →
      zeroZ ≤Z signed32 clz
      ∧
      ((shiftX : Word64) →
        unsignedZ shiftX ≡ signed32 clz →
        (shiftCountBounds shiftX
         ∧ valid nx (signed32 sx)
         ∧ valid x (signed32 sx)
         ∧ writeable nx ≡ true
         ∧ zeroZ <Z signed32 sx)
        ∧
        ((shiftedX : Ptr _ Word64) →
          sameShape shiftedX nx →
          (high : Word64) →
          addInt
              (value shiftedX (signed32 sx))
              (multiplyInt
                (powerInt radixZ (signed32 sx))
                (unsignedZ high))
            ≡ multiplyInt
                (value x (signed32 sx))
                (powerInt twoZ (unsignedZ shiftX)) →
          (accessAt shiftedX
             (addInt (off shiftedX) (signed32 sx))
           ∧ writeable shiftedX ≡ true)
          ∧
          ((extended : Ptr _ Word64) →
            sameShape extended shiftedX →
            updatedAtAndStored
              extended shiftedX
              (addInt (off extended) (signed32 sx))
              high →
            (adjustOne : Bool) →
            wordFlag adjust one32 adjustOne →
            int32InBounds
              (addInt (signed32 sx) (signed32 adjust))
            ∧
            ((total : Word32) →
              signed32 total
                ≡ addInt (signed32 sx) (signed32 adjust) →
              generalDivPreconditions sy total extended normalizedY q
              ∧ generalShiftedContinuation
                  sx sy adjust clz total scale
                  x y q extended normalizedY))))))

generalClzCase :
  {Zone : Set} →
  Word32 →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word64 →
  Set
generalClzCase sx sy adjust x y q nx ny mostSignificant =
  (clz : Word32) →
  clzConditions mostSignificant clz →
  let scale = powerInt twoZ (signed32 clz)
  in
  (zeroFlag : Bool) →
  wordFlag clz zero32 zeroFlag →
  IfSet
    zeroFlag
    (generalUnshifted sx sy adjust x y q nx)
    (generalShifted sx sy adjust clz scale x y q nx ny)

generalCase :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
generalCase sx sy x y q nx ny =
  int32InBounds (subtractInt (signed32 sy) oneZ)
  ∧
  ((yTop : Word32) →
    signed32 yTop ≡ subtractInt (signed32 sy) oneZ →
    accessAt y (addInt (off y) (signed32 yTop))
    ∧ int32InBounds (subtractInt (signed32 sx) oneZ)
    ∧
    ((xTop : Word32) →
      signed32 xTop ≡ subtractInt (signed32 sx) oneZ →
      accessAt x (addInt (off x) (signed32 xTop))
      ∧
      ((adjust : Word32) →
        IfSet
          (intLessOrEqual
            (unsignedZ (pelts y (addInt (off y) (signed32 yTop))))
            (unsignedZ (pelts x (addInt (off x) (signed32 xTop)))))
          (adjust ≡ one32)
          (adjust ≡ zero32) →
        int32InBounds (subtractInt (signed32 sy) oneZ)
        ∧
        ((yTopAgain : Word32) →
          signed32 yTopAgain
            ≡ subtractInt (signed32 sy) oneZ →
          accessAt y (addInt (off y) (signed32 yTopAgain))
          ∧
          (let mostSignificant =
                 pelts y (addInt (off y) (signed32 yTopAgain))
           in
           zeroZ <Z unsignedZ mostSignificant
           ∧ generalClzCase
               sx sy adjust x y q nx ny mostSignificant)))))

nonOneLimbBranch :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
nonOneLimbBranch sy sx x y q nx ny =
  (twoFlag : Bool) →
  wordFlag sy two32 twoFlag →
  IfSet
    twoFlag
    (twoLimbCase sx sy x y q nx ny)
    (generalCase sx sy x y q nx ny)

div-qr-in-place'vc : Set₁
div-qr-in-place'vc =
  (Zone : Set) →
  (sy sx : Word32) →
  (x y q nx ny : Ptr Zone Word64) →
  (oneFlag : Bool) →
  oneZ ≤Z signed32 sy →
  signed32 sy ≤Z signed32 sx →
  signed32 sx ≤Z subtractInt max32 oneZ →
  valid x (signed32 sx) →
  valid y (signed32 sy) →
  valid q
    (addInt
      (subtractInt (signed32 sx) (signed32 sy))
      oneZ) →
  valid nx (addInt (signed32 sx) oneZ) →
  valid ny (signed32 sy) →
  writeable q ≡ true →
  writeable x ≡ true →
  writeable nx ≡ true →
  writeable ny ≡ true →
  zeroZ <Z
    unsignedZ
      (pelts y
        (subtractInt
          (addInt (off y) (signed32 sy))
          oneZ)) →
  wordFlag sy one32 oneFlag →
  IfSet
    oneFlag
    (oneLimbBranch sy sx x y q)
    (nonOneLimbBranch sy sx x y q nx ny)
