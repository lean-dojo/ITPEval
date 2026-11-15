-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/powm_Powm_getbitqtvc: the verification condition for
-- extracting one bit from a multiprecision integer and relating it to the
-- bit-prefix value recurrence. This file contains no proof.

{-# OPTIONS --safe #-}

module powm_Powm_getbitqtvc where

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

zero64 : Word64
zero64 = replicateVec 64 false

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
ShiftedPointer shifted original o4 =
  off shifted ≡ addInt (off original) (signed32 o4)
  ∧ plength shifted ≡ plength original
  ∧ PeltsEqual shifted original
  ∧ contents shifted ≡ contents original
  ∧ lo shifted ≡ lo original
  ∧ hi shifted ≡ hi original
  ∧ region shifted ≡ region original
  ∧ writeable shifted ≡ writeable original

ResultObligation :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word64 →
  Set
ResultObligation p pn bi lps =
  (result : Word64) →
  unsignedZ result ≡ tmodInt (unsignedZ lps) twoZ →
  (zeroZ ≤Z unsignedZ result
   ∧ unsignedZ result ≤Z oneZ)
  ∧
  unsignedZ result ≡
    euclideanModuloPositive
      (euclideanDividePositive
        (value p (signed32 pn))
        (powerNat 2
          (intToNat (subtractInt (signed32 bi) oneZ))))
      2
  ∧
  valueB p (signed32 bi) ≡
    addInt
      (valueB p (subtractInt (signed32 bi) oneZ))
      (multiplyInt
        (powerZ 2 (subtractInt (signed32 bi) oneZ))
        (unsignedZ result))

ResObligation :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word64 →
  Set
ResObligation p pn bi lps =
  (res : Word64) →
  unsignedZ res ≡ tmodInt (unsignedZ lps) twoZ →
  Not (twoZ ≡ zeroZ)
  ∧
  (Not (twoZ ≡ zeroZ)
   ∧ uint64InBounds (tmodInt (unsignedZ lps) twoZ))
  ∧
  ResultObligation p pn bi lps

LpsObligation :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Set
LpsObligation p pn bi i mi =
  (lps : Word64) →
  unsignedZ lps ≡
    euclideanDividePositive
      (unsignedZ
        (pelts p (addInt (off p) (signed32 i))))
      (powerNat 2 (unsignedNat mi)) →
  Not (powerZ 2 (unsignedZ mi) ≡ zeroZ)
  ∧
  (Not (twoZ ≡ zeroZ)
   ∧ uint64InBounds (tmodInt (unsignedZ lps) twoZ))
  ∧
  ResObligation p pn bi lps

PPrimeObligation :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Word32 →
  Set
PPrimeObligation p pn bi i mi o4 =
  (p′ : Ptr _) →
  ShiftedPointer p′ p o4 →
  (zeroZ ≤Z unsignedZ mi ∧ unsignedZ mi <Z sixtyFourZ)
  ∧
  LpsObligation p pn bi i mi

O4Obligation :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Set
O4Obligation p pn bi i mi =
  (o4 : Word32) →
  signed32 o4 ≡ addInt (signed32 i) oneZ →
  (lo p ≤Z addInt (off p) (signed32 o4)
   ∧ addInt (off p) (signed32 o4) ≤Z hi p)
  ∧
  PPrimeObligation p pn bi i mi o4

MiObligation :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Set
MiObligation p pn bi i o3 =
  (mi : Word64) →
  unsignedZ mi ≡ tmodInt (unsignedZ o3) sixtyFourZ →
  (lo p ≤Z addInt (off p) (signed32 i)
   ∧ addInt (off p) (signed32 i) <Z hi p)
  ∧
  int32InBounds (addInt (signed32 i) oneZ)
  ∧
  O4Obligation p pn bi i mi

O2Obligation :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Set
O2Obligation p pn bi i =
  (o2 : Word32) →
  signed32 o2 ≡ subtractInt (signed32 bi) oneZ →
  zeroZ ≤Z signed32 o2
  ∧
  ((o3 : Word64) →
    unsignedZ o3 ≡ signed32 o2 →
    (Not (sixtyFourZ ≡ zeroZ)
     ∧ uint64InBounds (tmodInt (unsignedZ o3) sixtyFourZ))
    ∧
    MiObligation p pn bi i o3)

IObligation :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Set
IObligation p pn bi o1 =
  (i : Word32) →
  signed32 i ≡ tdivInt (signed32 o1) sixtyFourZ →
  int32InBounds (subtractInt (signed32 bi) oneZ)
  ∧
  O2Obligation p pn bi i

O1Obligation :
  {Zone : Set} →
  Ptr Zone →
  Word32 →
  Word32 →
  Set
O1Obligation p pn bi =
  (o1 : Word32) →
  signed32 o1 ≡ subtractInt (signed32 bi) oneZ →
  (Not (sixtyFourZ ≡ zeroZ)
   ∧ int32InBounds (tdivInt (signed32 o1) sixtyFourZ))
  ∧
  IObligation p pn bi o1

getbit'vc : Set₁
getbit'vc =
  (Zone : Set) →
  (p : Ptr Zone) →
  (pn bi : Word32) →
  valid p (signed32 pn) →
  oneZ ≤Z signed32 bi →
  euclideanDividePositive
    (addInt (signed32 bi) sixtyThreeZ)
    64
    ≤Z signed32 pn →
  int32InBounds (subtractInt (signed32 bi) oneZ)
  ∧
  O1Obligation p pn bi
