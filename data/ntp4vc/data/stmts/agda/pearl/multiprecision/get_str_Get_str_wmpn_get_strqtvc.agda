-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/get_str_Get_str_wmpn_get_strqtvc: the verification
-- condition for dispatching multiprecision integer conversion between the
-- power-of-two and arbitrary-base routines while preserving the digit-string
-- value, range, leading-digit, and pointer-frame contracts. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module get_str_Get_str_wmpn_get_strqtvc where

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

notBool : Bool → Bool
notBool false = true
notBool true = false

boolEqual : Bool → Bool → Bool
boolEqual false false = true
boolEqual false true = false
boolEqual true false = false
boolEqual true true = true

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

vecEqual : {n : Nat} → Vec Bool n → Vec Bool n → Bool
vecEqual []V []V = true
vecEqual (x ∷V xs) (y ∷V ys) with boolEqual x y
... | false = false
... | true = vecEqual xs ys

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

signed32 : Word32 → Int
signed32 bits with lastBit bits
... | false = unsignedZ bits
... | true = subtractInt (unsignedZ bits) (pos 4294967296)

zero32 : Word32
zero32 = natToVec 32 0

zeroZ oneZ twoZ sevenZ eightZ sixtyThreeZ sixtyFourZ twoFiftySixZ : Int
zeroZ = pos 0
oneZ = pos 1
twoZ = pos 2
sevenZ = pos 7
eightZ = pos 8
sixtyThreeZ = pos 63
sixtyFourZ = pos 64
twoFiftySixZ = pos 256

max32Z radixZ : Int
max32Z = pos 2147483647
radixZ = pos 18446744073709551616

min32Z : Int
min32Z = negsuc 2147483647

int32InBounds : Int → Set
int32InBounds value =
  min32Z ≤Z value ∧ value ≤Z max32Z

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
    (multiplyInt radixZ
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
    (unsignedZ (digits (addInt index (pos count))))
    (multiplyInt base (svalueMapFrom base digits index count))

svalueSub : Int → (Int → Word8) → Int → Int → Int
svalueSub base digits lower upper =
  svalueMapFrom base digits lower
    (intToNat (subtractInt upper lower))

svalue :
  {Zone : Set} → Int → Ptr Zone Word8 → Int → Int
svalue base p size =
  svalueSub base (pelts p) (off p) (addInt (off p) size)

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

record BaseInfo : Set where
  constructor base-info
  field
    b             : Int
    exp           : Word32
    bb            : Word64
    baseLower     : twoZ ≤Z b
    baseUpper     : b ≤Z twoFiftySixZ
    blockBelow    : unsignedZ bb <Z radixZ
    nextAtLeast   : radixZ ≤Z multiplyInt (unsignedZ bb) b
    exponentLower : sevenZ ≤Z unsignedZ exp
    exponentUpper : unsignedZ exp ≤Z sixtyThreeZ
    blockPower    : unsignedZ bb ≡ powerInt b (unsignedZ exp)

open BaseInfo public

topLimbPositive :
  {Zone : Set} → Ptr Zone Word64 → Word32 → Set
topLimbPositive up un =
  zeroZ <Z unsignedZ
    (pelts up
      (subtractInt
        (addInt (off up) (signed32 un))
        oneZ))

FinalPost :
  {Zone : Set} →
  Word32 → Word32 → Word32 →
  Ptr Zone Word64 → Ptr Zone Word8 → Word32 → Set
FinalPost base size un up current-sp result =
  inBase
    (signed32 base)
    (pelts current-sp)
    (off current-sp)
    (addInt (off current-sp) (unsignedZ result))
  ∧ svalue (signed32 base) current-sp (unsignedZ result)
      ≡ value up (signed32 un)
  ∧ (zeroZ <Z unsignedZ result
     ∧ unsignedZ result <Z signed32 size)
  ∧ zeroZ <Z unsignedZ (pelts current-sp (off current-sp))

PowerOfTwoSpec : Word64 → Word32 → Set
PowerOfTwoSpec base-limb bits =
  (zeroZ ≤Z unsignedZ bits ∧ unsignedZ bits ≤Z eightZ)
  ∧ (unsignedZ bits ≠ zeroZ →
      powerInt twoZ (unsignedZ bits) ≡ unsignedZ base-limb)
  ∧ (unsignedZ bits ≡ zeroZ →
      (n : Int) →
      zeroZ ≤Z n →
      powerInt twoZ n ≠ unsignedZ base-limb)

bitsCapacity : Word32 → Word32 → Int
bitsCapacity bit-count upper-bound =
  euclideanDivide
    (subtractInt
      (addInt (signed32 upper-bound) (unsignedZ bit-count))
      oneZ)
    (unsignedZ bit-count)

BitsCallPre :
  {Zone : Set} →
  Ptr Zone Word8 → Ptr Zone Word64 →
  Word32 → Word32 → Word32 → Set
BitsCallPre sp up un bits upper-bound =
  oneZ ≤Z signed32 un
  ∧ valid up (signed32 un)
  ∧ (oneZ ≤Z unsignedZ bits ∧ unsignedZ bits ≤Z eightZ)
  ∧ valid sp (bitsCapacity bits upper-bound)
  ∧ zeroZ ≤Z signed32 upper-bound
  ∧ value up (signed32 un)
      <Z powerInt twoZ (signed32 upper-bound)
  ∧ topLimbPositive up un
  ∧ addInt (multiplyInt sixtyFourZ (signed32 un)) sevenZ ≤Z max32Z
  ∧ writeable sp ≡ true

BitsResultPost :
  {Zone : Set} →
  Ptr Zone Word8 → Ptr Zone Word8 → Ptr Zone Word64 →
  Word32 → Word32 → Word32 → Word32 → Set
BitsResultPost original-sp current-sp up un bits upper-bound result =
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
     ∧ unsignedZ result ≤Z bitsCapacity bits upper-bound)
  ∧ zeroZ <Z unsignedZ (pelts current-sp (off current-sp))
  ∧ outsideUnchanged current-sp original-sp
      (bitsCapacity bits upper-bound)

BitsBranch :
  {Zone : Set} →
  Word32 → Word32 → Word32 →
  Ptr Zone Word8 → Ptr Zone Word64 → Word32 → Set
BitsBranch {Zone} base size un sp up bits =
  int32InBounds (multiplyInt sixtyFourZ (signed32 un))
  ∧ ((upper-bound : Word32) →
      signed32 upper-bound
        ≡ multiplyInt sixtyFourZ (signed32 un) →
      BitsCallPre sp up un bits upper-bound
      ∧ ((current-sp : Ptr Zone Word8) →
          sameFrame current-sp sp →
          (result : Word32) →
          BitsResultPost sp current-sp up un bits upper-bound result →
          FinalPost base size un up current-sp result))

OtherCallPre :
  {Zone : Set} →
  Word32 → Word32 → Word32 →
  Ptr Zone Word8 → Ptr Zone Word64 → BaseInfo → Set
OtherCallPre base size un sp up info =
  valid up (signed32 un)
  ∧ oneZ ≤Z signed32 un
  ∧ b info ≡ signed32 base
  ∧ writeable up ≡ true
  ∧ writeable sp ≡ true
  ∧ topLimbPositive up un
  ∧ zeroZ <Z signed32 size
  ∧ valid sp (signed32 size)
  ∧ value up (signed32 un)
      <Z powerInt
          (signed32 base)
          (subtractInt (signed32 size) oneZ)

OtherResultPost :
  {Zone : Set} →
  Word32 → Word32 → Word32 → Ptr Zone Word8 → Ptr Zone Word8 →
  Ptr Zone Word64 → Word32 → Set
OtherResultPost base size un original-sp current-sp up result =
  (zeroZ ≤Z unsignedZ result
   ∧ unsignedZ result <Z signed32 size)
  ∧ svalue (signed32 base) current-sp (unsignedZ result)
      ≡ value up (signed32 un)
  ∧ inBase
      (signed32 base)
      (pelts current-sp)
      (off current-sp)
      (addInt (off current-sp) (unsignedZ result))
  ∧ zeroZ <Z unsignedZ (pelts current-sp (off current-sp))
  ∧ outsideUnchanged current-sp original-sp (signed32 size)

OtherBranch :
  {Zone : Set} →
  Word32 → Word32 → Ptr Zone Word8 → Ptr Zone Word64 → Word32 → Set
OtherBranch {Zone} base un sp up size =
  zeroZ ≤Z signed32 base
  ∧ ((base-limb : Word64) →
      unsignedZ base-limb ≡ signed32 base →
      (twoZ ≤Z unsignedZ base-limb
       ∧ unsignedZ base-limb ≤Z twoFiftySixZ)
      ∧ ((info : BaseInfo) →
          b info ≡ unsignedZ base-limb →
          OtherCallPre base size un sp up info
          ∧ ((current-sp : Ptr Zone Word8) →
              sameFrame current-sp sp →
              (result : Word32) →
              OtherResultPost base size un sp current-sp up result →
              FinalPost base size un up current-sp result)))

Get-str-wmpn-get-str-statement : Set₁
Get-str-wmpn-get-str-statement =
  (Zone : Set) →
  (size : Word32) →
  (un : Word32) →
  (sp : Ptr Zone Word8) →
  (up : Ptr Zone Word64) →
  (base : Word32) →
  zeroZ <Z signed32 size →
  zeroZ <Z signed32 un →
  valid sp (signed32 size) →
  valid up (signed32 un) →
  writeable sp ≡ true →
  writeable up ≡ true →
  powerInt radixZ (signed32 un)
    ≤Z powerInt
        (signed32 base)
        (subtractInt (signed32 size) oneZ) →
  topLimbPositive up un →
  twoZ ≤Z signed32 base →
  signed32 base ≤Z twoFiftySixZ →
  addInt (multiplyInt sixtyFourZ (signed32 un)) sevenZ ≤Z max32Z →
  zeroZ ≤Z signed32 base
  ∧ ((base-limb : Word64) →
      unsignedZ base-limb ≡ signed32 base →
      (twoZ ≤Z unsignedZ base-limb
       ∧ unsignedZ base-limb ≤Z twoFiftySixZ)
      ∧ ((bits : Word32) →
          PowerOfTwoSpec base-limb bits →
          (unsignedZ bits ≡ zeroZ → bits ≡ zero32) →
          IfSet
            (notBool (vecEqual bits zero32))
            (BitsBranch base size un sp up bits)
            (OtherBranch base un sp up size)))
