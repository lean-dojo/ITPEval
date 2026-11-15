-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/powm_Powm_getbitsqtvc: the verification condition for
-- extracting a nonempty window of fewer than 64 bits from a multiprecision
-- integer, including cross-limb bounds and value-prefix equations. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module powm_Powm_getbitsqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; div-helper)

infix 4 _≤Z_ _<Z_ _≠_
infixr 5 _∷V_
infixr 3 _∧_

data Bottom : Set where

Not : Set → Set
Not A = A → Bottom

_≠_ : {A : Set} → A → A → Set
x ≠ y = Not (x ≡ y)

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

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

absoluteNat : Int → Nat
absoluteNat (pos n) = n
absoluteNat (negsuc n) = suc n

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

-- Signed quotient truncated toward zero, as used by machine integer division.
tdivInt : Int → Int → Int
tdivInt (pos _) (pos zero) = pos zero
tdivInt (pos n) (pos (suc m)) = pos (natDivide n (suc m))
tdivInt (pos n) (negsuc m) = negative (natDivide n (suc m))
tdivInt (negsuc _) (pos zero) = pos zero
tdivInt (negsuc n) (pos (suc m)) =
  negative (natDivide (suc n) (suc m))
tdivInt (negsuc n) (negsuc m) =
  pos (natDivide (suc n) (suc m))

-- Signed remainder with the dividend's sign, as used by machine remainder.
tmodInt : Int → Int → Int
tmodInt dividend divisor =
  subtractInt dividend (multiplyInt divisor (tdivInt dividend divisor))

-- Why3 Euclidean remainder for a nonnegative natural modulus.
euclideanModuloPositive : Int → Nat → Int
euclideanModuloPositive _ zero = pos zero
euclideanModuloPositive (pos n) d@(suc _) =
  pos (natModulo n d)
euclideanModuloPositive (negsuc n) d@(suc _) with natModulo (suc n) d
... | zero = pos zero
... | r@(suc _) = pos (d - r)

-- Why3 Euclidean quotient for a positive natural divisor.
euclideanDividePositive : Int → Nat → Int
euclideanDividePositive _ zero = pos zero
euclideanDividePositive dividend d@(suc _) =
  tdivInt
    (subtractInt dividend (euclideanModuloPositive dividend d))
    (pos d)

powerNat : Nat → Nat → Nat
powerNat base zero = 1
powerNat base (suc exponent) =
  base * powerNat base exponent

powerZ : Nat → Int → Int
powerZ base exponent =
  pos (powerNat base (intToNat exponent))

data Vec (A : Set) : Nat → Set where
  []V  : Vec A zero
  _∷V_ : {n : Nat} → A → Vec A n → Vec A (suc n)

replicateVec : {A : Set} → (n : Nat) → A → Vec A n
replicateVec zero value = []V
replicateVec (suc n) value = value ∷V replicateVec n value

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

zero64 one64 : Word64
zero64 = replicateVec 64 false
one64 = true ∷V replicateVec 63 false

signed32 : Word32 → Int
signed32 bits with lastBit bits
... | false = unsignedZ bits
... | true =
  subtractInt (unsignedZ bits) (pos 4294967296)

zeroZ oneZ twoZ sixtyThreeZ sixtyFourZ radixZ max64Z max32Z : Int
zeroZ = pos 0
oneZ = pos 1
twoZ = pos 2
sixtyThreeZ = pos 63
sixtyFourZ = pos 64
radixZ = pos 18446744073709551616
max64Z = pos 18446744073709551615
max32Z = pos 2147483647

min32Z : Int
min32Z = negsuc 2147483647

radixNat : Nat
radixNat = 18446744073709551616

int32InBounds : Int → Set
int32InBounds value =
  min32Z ≤Z value ∧ value ≤Z max32Z

uint64InBounds : Int → Set
uint64InBounds value =
  zeroZ ≤Z value ∧ value ≤Z max64Z

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

nthList : {A : Set} → A → Nat → List A → A
nthList default index [] = default
nthList default zero (x ∷ xs) = x
nthList default (suc index) (_ ∷ xs) =
  nthList default index xs

record Ptr (Zone : Set) : Set where
  constructor pointer
  field
    contents  : List Word64
    off       : Int
    lo        : Int
    hi        : Int
    region    : Zone
    writeable : Bool

open Ptr public

pelts : {Zone : Set} → Ptr Zone → Int → Word64
pelts p index =
  nthList zero64 (intToNat index) (contents p)

plength : {Zone : Set} → Ptr Zone → Int
plength p = pos (listLength (contents p))

valid : {Zone : Set} → Ptr Zone → Int → Set
valid p size =
  int32InBounds size
  ∧ zeroZ ≤Z size
  ∧ (zeroZ ≤Z lo p ∧ lo p ≤Z off p)
  ∧ addInt (off p) size ≤Z hi p
  ∧ hi p ≤Z plength p

PeltsEqual : {Zone : Set} → Ptr Zone → Ptr Zone → Set
PeltsEqual p q =
  (index : Int) → pelts p index ≡ pelts q index

valueFrom :
  {Zone : Set} →
  Ptr Zone →
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
  Ptr Zone →
  Int →
  Int
value p size =
  valueFrom p (off p) (intToNat size)

valueB :
  {Zone : Set} →
  Ptr Zone →
  Int →
  Int
valueB p bit-count with intLess bit-count zeroZ
... | true = zeroZ
... | false =
  let limb-index =
        euclideanDividePositive bit-count 64
      low-bit-count =
        subtractInt bit-count
          (multiplyInt sixtyFourZ limb-index)
      partial-limb =
        euclideanModuloPositive
          (unsignedZ
            (pelts p (addInt (off p) limb-index)))
          (powerNat 2 (intToNat low-bit-count))
  in
  addInt
    (value p limb-index)
    (multiplyInt
      (powerZ radixNat limb-index)
      partial-limb)

ShiftedPointer :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Set
ShiftedPointer shifted original amount =
  off shifted ≡ addInt (off original) (signed32 amount)
  ∧ plength shifted ≡ plength original
  ∧ PeltsEqual shifted original
  ∧ contents shifted ≡ contents original
  ∧ lo shifted ≡ lo original
  ∧ hi shifted ≡ hi original
  ∧ region shifted ≡ region original
  ∧ writeable shifted ≡ writeable original

ResultSpecification :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Set
ResultSpecification p pn bi nbits result =
  (signed32 nbits ≤Z signed32 bi →
    valueB p (signed32 bi) ≡
      addInt
        (valueB p
          (subtractInt (signed32 bi) (signed32 nbits)))
        (multiplyInt
          (powerZ 2
            (subtractInt (signed32 bi) (signed32 nbits)))
          (unsignedZ result)))
  ∧
  (signed32 bi <Z signed32 nbits →
    valueB p (signed32 bi) ≡ unsignedZ result)
  ∧
  (zeroZ ≤Z unsignedZ result
   ∧ unsignedZ result <Z
      powerZ 2 (signed32 nbits))
  ∧
  (signed32 nbits ≤Z signed32 bi →
    unsignedZ result ≡
      euclideanModuloPositive
        (euclideanDividePositive
          (value p (signed32 pn))
          (powerNat 2
            (intToNat
              (subtractInt
                (signed32 bi)
                (signed32 nbits)))))
        (powerNat 2 (intToNat (signed32 nbits))))

ResultFrom :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Int →
  Int →
  Set
ResultFrom p pn bi nbits numerator divisor =
  (result : Word64) →
  unsignedZ result ≡ tmodInt numerator divisor →
  ResultSpecification p pn bi nbits result

MaskObligation :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Int →
  Word64 →
  Set
MaskObligation p pn bi nbits numerator exponent =
  (mask : Word64) →
  unsignedZ mask ≡
    multiplyInt
      (powerZ 2 (unsignedZ exponent))
      (unsignedZ one64) →
  (Not (unsignedZ mask ≡ zeroZ)
   ∧ uint64InBounds
      (tmodInt numerator (unsignedZ mask)))
  ∧ ResultFrom
      p pn bi nbits numerator (unsignedZ mask)

ExponentObligation :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Int →
  Set
ExponentObligation p pn bi nbits numerator =
  (exponent : Word64) →
  unsignedZ exponent ≡ signed32 nbits →
  ((zeroZ ≤Z unsignedZ exponent
    ∧ unsignedZ exponent <Z sixtyFourZ)
   ∧
   multiplyInt
     (powerZ 2 (unsignedZ exponent))
     (unsignedZ one64)
     ≤Z max64Z)
  ∧ MaskObligation p pn bi nbits numerator exponent

NBitsResult :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Int →
  Set
NBitsResult p pn bi nbits numerator =
  zeroZ ≤Z signed32 nbits
  ∧ ExponentObligation p pn bi nbits numerator

InitialMaskObligation :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Set
InitialMaskObligation p pn bi nbits exponent =
  (mask : Word64) →
  unsignedZ mask ≡
    multiplyInt
      (powerZ 2 (unsignedZ exponent))
      (unsignedZ one64) →
  (lo p ≤Z off p ∧ off p <Z hi p)
  ∧
  let first-limb = pelts p (off p)
  in
  (Not (unsignedZ mask ≡ zeroZ)
   ∧ uint64InBounds
      (tmodInt (unsignedZ first-limb) (unsignedZ mask)))
  ∧ ResultFrom
      p pn bi nbits
      (unsignedZ first-limb)
      (unsignedZ mask)

InitialExponentObligation :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Set
InitialExponentObligation p pn bi nbits =
  (exponent : Word64) →
  unsignedZ exponent ≡ signed32 bi →
  ((zeroZ ≤Z unsignedZ exponent
    ∧ unsignedZ exponent <Z sixtyFourZ)
   ∧
   multiplyInt
     (powerZ 2 (unsignedZ exponent))
     (unsignedZ one64)
     ≤Z max64Z)
  ∧ InitialMaskObligation p pn bi nbits exponent

ShortWindowBranch :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Set
ShortWindowBranch p pn bi nbits =
  zeroZ ≤Z signed32 bi
  ∧ InitialExponentObligation p pn bi nbits

PDoublePrimeObligation :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Word64 →
  Word32 →
  Set
PDoublePrimeObligation p pn bi nbits shifted-part shifted-in o9 =
  (p″ : Ptr _) →
  ShiftedPointer p″ p o9 →
  Not (radixZ ≡ zeroZ)
  ∧ uint64InBounds
      (addInt
        (unsignedZ shifted-part)
        (unsignedZ shifted-in))
  ∧
  ((combined : Word64) →
    unsignedZ combined ≡
      addInt
        (unsignedZ shifted-part)
        (unsignedZ shifted-in) →
    NBitsResult p pn bi nbits (unsignedZ combined))

O9Obligation :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Word64 →
  Set
O9Obligation p pn bi nbits limb-index shifted-part shifted-in =
  (o9 : Word32) →
  signed32 o9 ≡ addInt (signed32 limb-index) twoZ →
  (lo p ≤Z addInt (off p) (signed32 o9)
   ∧ addInt (off p) (signed32 o9) ≤Z hi p)
  ∧ PDoublePrimeObligation
      p pn bi nbits shifted-part shifted-in o9

ShiftedInObligation :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Word64 →
  Set
ShiftedInObligation
  p pn bi nbits quotient-index read-index shifted-part exponent =
  (shifted-in : Word64) →
  (unsignedZ shifted-in ≡
      euclideanModuloPositive
        (multiplyInt
          (unsignedZ
            (pelts p
              (addInt (off p) (signed32 read-index))))
          (powerZ 2 (unsignedZ exponent)))
        radixNat
   ∧
   unsignedZ shifted-in ≤Z
     subtractInt
       radixZ
       (powerZ 2 (unsignedZ exponent))) →
  int32InBounds (addInt (signed32 quotient-index) twoZ)
  ∧ O9Obligation
      p pn bi nbits quotient-index shifted-part shifted-in

CrossExponentObligation :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Set
CrossExponentObligation
  p pn bi nbits quotient-index read-index nbits-in-r shifted-part =
  (exponent : Word64) →
  unsignedZ exponent ≡ signed32 nbits-in-r →
  ((zeroZ ≤Z unsignedZ exponent
    ∧ unsignedZ exponent <Z sixtyFourZ)
   ∧
   multiplyInt
     (powerZ 2 (unsignedZ exponent))
     (unsignedZ one64)
     ≤Z max64Z)
  ∧ ShiftedInObligation
      p pn bi nbits quotient-index read-index shifted-part exponent

O7Obligation :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Word32 →
  Set
O7Obligation p pn bi nbits limb-index shifted-part nbits-in-r =
  (o7 : Word32) →
  signed32 o7 ≡ addInt (signed32 limb-index) oneZ →
  (lo p ≤Z addInt (off p) (signed32 o7)
   ∧ addInt (off p) (signed32 o7) <Z hi p)
  ∧ zeroZ ≤Z signed32 nbits-in-r
  ∧ CrossExponentObligation
      p pn bi nbits limb-index o7 nbits-in-r shifted-part

CrossLimbBranch :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Word32 →
  Set
CrossLimbBranch p pn bi nbits limb-index shifted-part nbits-in-r =
  int32InBounds (addInt (signed32 limb-index) oneZ)
  ∧ O7Obligation
      p pn bi nbits limb-index shifted-part nbits-in-r

NBitsInRObligation :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Set
NBitsInRObligation
  p pn bi nbits quotient-index remainder-index shifted-part =
  (nbits-in-r : Word32) →
  signed32 nbits-in-r ≡
    subtractInt sixtyFourZ (signed32 remainder-index) →
  IfSet
    (intLess (signed32 nbits-in-r) (signed32 nbits))
    (CrossLimbBranch
      p pn bi nbits quotient-index shifted-part nbits-in-r)
    (NBitsResult p pn bi nbits (unsignedZ shifted-part))

ShiftedPartObligation :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Set
ShiftedPartObligation
  p pn bi nbits quotient-index remainder-index remainder-limb =
  (shifted-part : Word64) →
  unsignedZ shifted-part ≡
    euclideanDividePositive
      (unsignedZ
        (pelts p
          (addInt (off p) (signed32 quotient-index))))
      (powerNat 2 (unsignedNat remainder-limb)) →
  Not (powerZ 2 (signed32 remainder-index) ≡ zeroZ)
  ∧ int32InBounds
      (subtractInt sixtyFourZ (signed32 remainder-index))
  ∧ NBitsInRObligation
      p pn bi nbits quotient-index remainder-index shifted-part

RemainderAsLimbObligation :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Set
RemainderAsLimbObligation p pn bi nbits quotient-index remainder-index =
  (remainder-limb : Word64) →
  unsignedZ remainder-limb ≡ signed32 remainder-index →
  (zeroZ ≤Z unsignedZ remainder-limb
   ∧ unsignedZ remainder-limb <Z sixtyFourZ)
  ∧ ShiftedPartObligation
      p pn bi nbits quotient-index remainder-index remainder-limb

PPrimeObligation :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Set
PPrimeObligation p pn bi nbits quotient-index remainder-index o4 =
  (p′ : Ptr _) →
  ShiftedPointer p′ p o4 →
  zeroZ ≤Z signed32 remainder-index
  ∧ RemainderAsLimbObligation
      p pn bi nbits quotient-index remainder-index

O4Obligation :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Set
O4Obligation p pn bi nbits quotient-index remainder-index =
  (o4 : Word32) →
  signed32 o4 ≡ addInt (signed32 quotient-index) oneZ →
  (lo p ≤Z addInt (off p) (signed32 o4)
   ∧ addInt (off p) (signed32 o4) ≤Z hi p)
  ∧ PPrimeObligation
      p pn bi nbits quotient-index remainder-index o4

RemainderIndexObligation :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Set
RemainderIndexObligation p pn bi nbits quotient-index =
  (remainder-index : Word32) →
  signed32 remainder-index ≡
    tmodInt
      (subtractInt (signed32 bi) (signed32 nbits))
      sixtyFourZ →
  (lo p ≤Z
      addInt (off p) (signed32 quotient-index)
   ∧
   addInt (off p) (signed32 quotient-index) <Z hi p)
  ∧ int32InBounds
      (addInt (signed32 quotient-index) oneZ)
  ∧ O4Obligation
      p pn bi nbits quotient-index remainder-index

DifferenceWordObligation :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Set
DifferenceWordObligation p pn bi nbits =
  (difference-word : Word32) →
  signed32 difference-word ≡
    subtractInt (signed32 bi) (signed32 nbits) →
  (Not (sixtyFourZ ≡ zeroZ)
   ∧ int32InBounds
      (tdivInt (signed32 difference-word) sixtyFourZ))
  ∧
  ((quotient-index : Word32) →
    signed32 quotient-index ≡
      tdivInt (signed32 difference-word) sixtyFourZ →
    (Not (sixtyFourZ ≡ zeroZ)
     ∧ int32InBounds
        (tmodInt (signed32 difference-word) sixtyFourZ))
    ∧
    ((remainder-index : Word32) →
      signed32 remainder-index ≡
        tmodInt (signed32 difference-word) sixtyFourZ →
      (lo p ≤Z
        addInt (off p) (signed32 quotient-index)
       ∧
       addInt (off p) (signed32 quotient-index) <Z hi p)
      ∧ int32InBounds
          (addInt (signed32 quotient-index) oneZ)
      ∧ O4Obligation
          p pn bi nbits quotient-index remainder-index))

LongWindowBranch :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Set
LongWindowBranch p pn bi nbits =
  int32InBounds
    (subtractInt (signed32 bi) (signed32 nbits))
  ∧ DifferenceWordObligation p pn bi nbits

getbits'vc : Set₁
getbits'vc =
  (Zone : Set) →
  (nbits bi pn : Word32) →
  (p : Ptr Zone) →
  oneZ ≤Z signed32 nbits →
  signed32 nbits <Z sixtyFourZ →
  zeroZ ≤Z signed32 bi →
  oneZ ≤Z signed32 pn →
  valid p (signed32 pn) →
  euclideanDividePositive
    (addInt (signed32 bi) sixtyThreeZ)
    64
    ≤Z signed32 pn →
  IfSet
    (intLess (signed32 bi) (signed32 nbits))
    (ShortWindowBranch p pn bi nbits)
    (LongWindowBranch p pn bi nbits)
