-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/get_str_Get_str_wmpn_get_str_otherqtvc: the verification
-- condition for converting a multiprecision integer to digits in an arbitrary
-- base, including division and padding loops, byte reversal, pointer frames,
-- fixed-width conversions, and the final string-value contract. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module get_str_Get_str_wmpn_get_str_otherqtvc where

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

zero8 : Word8
zero8 = natToVec 8 0

zero32 one32 : Word32
zero32 = natToVec 32 0
one32 = natToVec 32 1

zeroZ oneZ twoZ sevenZ sixtyThreeZ sixtyFourZ twoFiftySixZ : Int
zeroZ = pos 0
oneZ = pos 1
twoZ = pos 2
sevenZ = pos 7
sixtyThreeZ = pos 63
sixtyFourZ = pos 64
twoFiftySixZ = pos 256

max32Z maxUnsigned32Z radixZ max64Z : Int
max32Z = pos 2147483647
maxUnsigned32Z = pos 4294967295
radixZ = pos 18446744073709551616
max64Z = pos 18446744073709551615

min32Z : Int
min32Z = negsuc 2147483647

int32InBounds : Int → Set
int32InBounds value =
  min32Z ≤Z value ∧ value ≤Z max32Z

uint32InBounds : Int → Set
uint32InBounds value =
  zeroZ ≤Z value ∧ value ≤Z maxUnsigned32Z

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

shiftedPointer :
  {Zone A : Set} → Ptr Zone A → Ptr Zone A → Int → Set
shiftedPointer shifted original amount =
  off shifted ≡ addInt (off original) amount
  ∧ cellCount shifted ≡ cellCount original
  ∧ FunctionEqual (pelts shifted) (pelts original)
  ∧ lo shifted ≡ lo original
  ∧ hi shifted ≡ hi original
  ∧ region shifted ≡ region original
  ∧ writeable shifted ≡ writeable original

mapEqSubShift :
  {A : Set} →
  (Int → A) → (Int → A) → Int → Int → Int → Set
mapEqSubShift x y xi yi size =
  (i : Int) →
  (zeroZ ≤Z i ∧ i <Z size) →
  x (addInt xi i) ≡ y (addInt yi i)

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

svalueLeMapFrom : Int → (Int → Word8) → Int → Nat → Int
svalueLeMapFrom base digits index zero = zeroZ
svalueLeMapFrom base digits index (suc count) =
  addInt
    (unsignedZ (digits index))
    (multiplyInt base
      (svalueLeMapFrom base digits (addInt index oneZ) count))

svalueLeSub : Int → (Int → Word8) → Int → Int → Int
svalueLeSub base digits lower upper =
  svalueLeMapFrom base digits lower
    (intToNat (subtractInt upper lower))

svalueLe :
  {Zone : Set} → Int → Ptr Zone Word8 → Int → Int
svalueLe base p size =
  svalueLeSub base (pelts p) (off p) (addInt (off p) size)

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

reciprocal : Word64 → Word64 → Set
reciprocal inverse divisor =
  unsignedZ inverse ≡
  subtractInt
    (euclideanDivide
      (subtractInt (multiplyInt radixZ radixZ) oneZ)
      (unsignedZ divisor))
    radixZ

DivisionResult :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word64 → Word64 → Set
DivisionResult quotient dividend count divisor remainder =
  value dividend (signed32 count)
    ≡ addInt
        (multiplyInt
          (value quotient (signed32 count))
          (unsignedZ divisor))
        (unsignedZ remainder)
  ∧ unsignedZ remainder <Z unsignedZ divisor

allocated :
  {Zone A : Set} → Ptr Zone A → Int → Set
allocated p count =
  plength p ≡ count
  ∧ off p ≡ zeroZ
  ∧ lo p ≡ zeroZ
  ∧ hi p ≡ count
  ∧ writeable p ≡ true

LimbDigitsPost :
  {Zone : Set} →
  Int → Ptr Zone Word8 → Ptr Zone Word8 →
  Int → Word64 → Word32 → Set
LimbDigitsPost base before after capacity input done =
  svalueLe base after (unsignedZ done) ≡ unsignedZ input
  ∧ (zeroZ ≤Z unsignedZ done ∧ unsignedZ done ≤Z capacity)
  ∧ (zeroZ <Z unsignedZ done →
      zeroZ <Z unsignedZ
        (pelts after
          (subtractInt
            (addInt (off after) (unsignedZ done)) oneZ)))
  ∧ outsideUnchanged after before (unsignedZ done)
  ∧ inBase base (pelts after) (off after)
      (addInt (off after) (unsignedZ done))

PartialPost :
  {Zone : Set} →
  Int → Int → Ptr Zone Word8 → Word32 →
  Ptr Zone Word64 → Ptr Zone Word8 → Word32 → Set
PartialPost total base original-sp size up current-sp sn =
  addInt
    (svalueLe base current-sp (signed32 sn))
    (multiplyInt
      (powerInt base (signed32 sn))
      (value up oneZ))
    ≡ total
  ∧ inBase base (pelts current-sp) (off current-sp)
      (addInt (off current-sp) (signed32 sn))
  ∧ (zeroZ ≤Z signed32 sn ∧ signed32 sn <Z signed32 size)
  ∧ zeroZ <Z value up oneZ
  ∧ outsideUnchanged current-sp original-sp (signed32 size)

OuterInvariant :
  {Zone : Set} →
  Int → Int → BaseInfo → Word32 → Word32 →
  Ptr Zone Word8 → Ptr Zone Word64 → Int →
  Ptr Zone Word64 → Word32 → Ptr Zone Word8 → Word32 → Set
OuterInvariant total base info un size original-sp original-up loop-index
  current-up n current-sp sn =
  addInt
    (svalueLe base current-sp (signed32 sn))
    (multiplyInt
      (powerInt base (signed32 sn))
      (value current-up (signed32 n)))
    ≡ total
  ∧ (oneZ ≤Z signed32 n ∧ signed32 n ≤Z signed32 un)
  ∧ subtractInt (signed32 un) (signed32 n) ≤Z loop-index
  ∧ (zeroZ ≤Z signed32 sn ∧ signed32 sn <Z signed32 size)
  ∧ signed32 sn ≡ multiplyInt loop-index (unsignedZ (exp info))
  ∧ inBase base (pelts current-sp) (off current-sp)
      (addInt (off current-sp) (signed32 sn))
  ∧ zeroZ <Z unsignedZ
      (pelts current-up
        (subtractInt
          (addInt (off current-up) (signed32 n)) oneZ))
  ∧ outsideUnchanged current-sp original-sp (signed32 size)

PaddingInvariant :
  {Zone : Set} →
  Int → Int → BaseInfo → Word32 →
  Ptr Zone Word8 → Ptr Zone Word64 → Word32 →
  Word32 → Word32 → Word32 → Ptr Zone Word8 → Set
PaddingInvariant total base info size original-sp current-up n
  initial-sn done current-sn current-sp =
  unsignedZ done ≤Z unsignedZ (exp info)
  ∧ signed32 current-sn
      ≡ addInt (signed32 initial-sn) (unsignedZ done)
  ∧ inBase base (pelts current-sp) (off current-sp)
      (addInt (off current-sp) (signed32 current-sn))
  ∧ addInt
      (svalueLe base current-sp (signed32 current-sn))
      (multiplyInt
        (powerInt base
          (addInt
            (subtractInt (signed32 current-sn) (unsignedZ done))
            (unsignedZ (exp info))))
        (value current-up (signed32 n)))
      ≡ total
  ∧ outsideUnchanged current-sp original-sp (signed32 size)

ReverseInvariant :
  {Zone : Set} →
  Int → Word32 → Ptr Zone Word8 → Ptr Zone Word8 →
  Ptr Zone Word8 → Word32 → Word32 → Set
ReverseInvariant base size global-original reversal-original current total i =
  (zeroZ ≤Z addInt (multiplyInt twoZ (signed32 i)) oneZ
   ∧ addInt (multiplyInt twoZ (signed32 i)) oneZ
      ≤Z addInt (signed32 total) oneZ)
  ∧ ((j : Int) →
      (addInt (off current) (signed32 i) ≤Z j
       ∧ j <Z subtractInt
          (addInt (off current) (signed32 total)) (signed32 i)) →
      pelts current j ≡ pelts reversal-original j)
  ∧ inBase base (pelts current) (off current)
      (addInt (off current) (signed32 total))
  ∧ svalueSub base (pelts current) (off current)
      (addInt (off current) (signed32 i))
      ≡ svalueLeSub base (pelts reversal-original)
          (subtractInt
            (addInt (off current) (signed32 total)) (signed32 i))
          (addInt (off current) (signed32 total))
  ∧ svalueSub base (pelts current)
      (subtractInt
        (addInt (off current) (signed32 total)) (signed32 i))
      (addInt (off current) (signed32 total))
      ≡ svalueLeSub base (pelts reversal-original) (off current)
          (addInt (off current) (signed32 i))
  ∧ svalueLeSub base (pelts current)
      (addInt (off current) (signed32 i))
      (subtractInt
        (addInt (off current) (signed32 total)) (signed32 i))
      ≡ svalueLeSub base (pelts reversal-original)
          (addInt (off current) (signed32 i))
          (subtractInt
            (addInt (off current) (signed32 total)) (signed32 i))
  ∧ (zeroZ <Z signed32 i →
      zeroZ <Z unsignedZ (pelts current (off current)))
  ∧ outsideUnchanged current global-original (signed32 size)

FinalPost :
  {Zone : Set} →
  Int → Ptr Zone Word64 → Word32 →
  Ptr Zone Word8 → Word32 → Ptr Zone Word8 → Word32 → Set
FinalPost base original-up un original-sp size current result =
  (zeroZ ≤Z unsignedZ result ∧ unsignedZ result <Z signed32 size)
  ∧ svalue base current (unsignedZ result)
      ≡ value original-up (signed32 un)
  ∧ inBase base (pelts current) (off current)
      (addInt (off current) (unsignedZ result))
  ∧ zeroZ <Z unsignedZ (pelts current (off current))
  ∧ outsideUnchanged current original-sp (signed32 size)

ReverseStep :
  {Zone : Set} →
  Int → Ptr Zone Word64 → Word32 →
  Ptr Zone Word8 → Word32 → Ptr Zone Word8 →
  Word32 → Ptr Zone Word8 → Word32 → Set
ReverseStep {Zone} base original-up un original-sp size reversal-original
  total current i =
  int32InBounds (multiplyInt twoZ (signed32 i))
  ∧ ((twice : Word32) →
      signed32 twice ≡ multiplyInt twoZ (signed32 i) →
      int32InBounds (addInt (signed32 twice) oneZ)
      ∧ ((test : Word32) →
          signed32 test ≡ addInt (signed32 twice) oneZ →
          IfSet (intLess (signed32 test) (signed32 total))
            (accessAt current (addInt (off current) (signed32 i))
             ∧ ((saved : Word8) →
                saved ≡ pelts current
                  (addInt (off current) (signed32 i)) →
                int32InBounds
                  (subtractInt (signed32 total) (signed32 i))
                ∧ ((from-end : Word32) →
                    signed32 from-end ≡
                      subtractInt (signed32 total) (signed32 i) →
                    int32InBounds
                      (subtractInt (signed32 from-end) oneZ)
                    ∧ ((mirror : Word32) →
                        signed32 mirror ≡
                          subtractInt (signed32 from-end) oneZ →
                        accessAt current
                          (addInt (off current) (signed32 mirror))
                        ∧ ((other : Word8) →
                            other ≡ pelts current
                              (addInt (off current) (signed32 mirror)) →
                            (accessAt current
                              (addInt (off current) (signed32 i))
                             ∧ writeable current ≡ true)
                            ∧ ((after-first : Ptr Zone Word8) →
                                sameFrame after-first current →
                                FunctionEqual (pelts after-first)
                                  (update (pelts current)
                                    (addInt (off after-first)
                                      (signed32 i)) other)
                                ∧ pelts after-first
                                    (addInt (off after-first)
                                      (signed32 i)) ≡ other →
                                int32InBounds
                                  (subtractInt
                                    (signed32 total) (signed32 i))
                                ∧ ((from-end-again : Word32) →
                                    signed32 from-end-again ≡
                                      subtractInt
                                        (signed32 total) (signed32 i) →
                                    int32InBounds
                                      (subtractInt
                                        (signed32 from-end-again) oneZ)
                                    ∧ ((mirror-again : Word32) →
                                        signed32 mirror-again ≡
                                          subtractInt
                                            (signed32 from-end-again) oneZ →
                                        (accessAt after-first
                                          (addInt (off after-first)
                                            (signed32 mirror-again))
                                         ∧ writeable after-first ≡ true)
                                        ∧ ((after-second :
                                              Ptr Zone Word8) →
                                            sameFrame after-second after-first →
                                            FunctionEqual
                                              (pelts after-second)
                                              (update
                                                (pelts after-first)
                                                (addInt
                                                  (off after-second)
                                                  (signed32 mirror-again))
                                                saved)
                                            ∧ pelts after-second
                                                (addInt
                                                  (off after-second)
                                                  (signed32 mirror-again))
                                                ≡ saved →
                                            int32InBounds
                                              (addInt (signed32 i) oneZ)
                                            ∧ ((next-i : Word32) →
                                                signed32 next-i ≡
                                                  addInt
                                                    (signed32 i) oneZ →
                                                (zeroZ ≤Z
                                                  subtractInt
                                                    (signed32 total)
                                                    (signed32 i)
                                                 ∧ subtractInt
                                                    (signed32 total)
                                                    (signed32 next-i)
                                                    <Z subtractInt
                                                      (signed32 total)
                                                      (signed32 i))
                                                ∧ ReverseInvariant
                                                    base size original-sp
                                                    reversal-original
                                                    after-second total next-i))))))))))
            (zeroZ ≤Z signed32 total
             ∧ ((result : Word32) →
                unsignedZ result ≡ signed32 total →
                FinalPost base original-up un original-sp size
                  current result))))

ReverseLoop :
  {Zone : Set} →
  Int → Ptr Zone Word64 → Word32 →
  Ptr Zone Word8 → Word32 → Ptr Zone Word8 → Word32 → Set
ReverseLoop {Zone} base original-up un original-sp size reversal-original total =
  ReverseInvariant base size original-sp reversal-original
    reversal-original total zero32
  ∧ ((i : Word32) (current : Ptr Zone Word8) →
      sameFrame current reversal-original →
      ReverseInvariant base size original-sp reversal-original current total i →
      ReverseStep base original-up un original-sp size reversal-original
        total current i)

FinalLimbPhase :
  {Zone : Set} →
  Int → Ptr Zone Word64 → Word32 → BaseInfo →
  Ptr Zone Word8 → Word32 → Word64 → Word64 → Word64 →
  Ptr Zone Word64 → Ptr Zone Word8 → Word32 → Set
FinalLimbPhase {Zone} base original-up un info original-sp size shift d1 di
  current-up current-sp sn =
  accessAt current-up (off current-up)
  ∧ ((last-limb : Word64) →
      last-limb ≡ pelts current-up (off current-up) →
      (lo current-sp ≤Z addInt (off current-sp) (signed32 sn)
       ∧ addInt (off current-sp) (signed32 sn) ≤Z hi current-sp)
      ∧ ((spn : Ptr Zone Word8) →
          shiftedPointer spn current-sp (signed32 sn) →
          int32InBounds (subtractInt (signed32 size) oneZ)
          ∧ ((size-minus-one : Word32) →
              signed32 size-minus-one ≡
                subtractInt (signed32 size) oneZ →
              int32InBounds
                (subtractInt
                  (signed32 size-minus-one) (signed32 sn))
              ∧ ((capacity : Word32) →
                  signed32 capacity ≡
                    subtractInt
                      (signed32 size-minus-one) (signed32 sn) →
                  ((twoZ ≤Z b info ∧ b info ≤Z twoFiftySixZ)
                   ∧ writeable spn ≡ true
                   ∧ euclideanDivide radixZ twoZ ≤Z unsignedZ d1
                   ∧ (zeroZ ≤Z unsignedZ shift
                      ∧ unsignedZ shift ≤Z sixtyThreeZ)
                   ∧ multiplyInt (b info)
                        (powerInt twoZ (unsignedZ shift))
                        ≡ unsignedZ d1
                   ∧ reciprocal di d1
                   ∧ valid spn (signed32 capacity)
                   ∧ zeroZ <Z signed32 capacity
                   ∧ unsignedZ last-limb
                        <Z powerInt (b info) (signed32 capacity))
                  ∧ ((after-local returned : Ptr Zone Word8) →
                      FunctionEqual (pelts after-local) (pelts returned)
                      ∧ sameFrame after-local spn →
                      sameFrame returned current-sp →
                      (done : Word32) →
                      LimbDigitsPost (b info) spn after-local
                        (signed32 capacity) last-limb done →
                      unsignedZ done ≤Z max32Z
                      ∧ ((done-signed : Word32) →
                          signed32 done-signed ≡ unsignedZ done →
                          int32InBounds
                            (addInt
                              (signed32 sn) (signed32 done-signed))
                          ∧ ((total : Word32) →
                              signed32 total ≡
                                addInt
                                  (signed32 sn) (signed32 done-signed) →
                              ReverseLoop base original-up un original-sp
                                size returned total)))))))

FinalContinuation :
  {Zone : Set} →
  Int → Int → Ptr Zone Word64 → Word32 → BaseInfo →
  Ptr Zone Word8 → Word32 → Word64 → Word64 → Word64 → Set
FinalContinuation {Zone} total base original-up un info original-sp size shift d1 di =
  (sn : Word32) (current-up : Ptr Zone Word64)
  (current-sp : Ptr Zone Word8) →
  sameFrame current-up original-up →
  sameFrame current-sp original-sp →
  PartialPost total base original-sp size current-up current-sp sn →
  FinalLimbPhase base original-up un info original-sp size shift d1 di
    current-up current-sp sn

PaddingStep :
  {Zone : Set} →
  Int → Int → BaseInfo → Ptr Zone Word8 → Word32 →
  Word32 → Ptr Zone Word64 → Word32 → Word32 → Word32 →
  Ptr Zone Word8 → Word32 → Ptr Zone Word64 → Word32 → Int → Set
PaddingStep {Zone} total base info original-sp size un current-up n initial-sn
  done current-sp current-sn previous-up previous-n loop-index =
  IfSet (intLess (unsignedZ done) (unsignedZ (exp info)))
    ((accessAt current-sp
        (addInt (off current-sp) (signed32 current-sn))
      ∧ writeable current-sp ≡ true)
     ∧ ((after-zero : Ptr Zone Word8) →
        sameFrame after-zero current-sp →
        FunctionEqual (pelts after-zero)
          (update (pelts current-sp)
            (addInt (off after-zero) (signed32 current-sn)) zero8)
        ∧ pelts after-zero
            (addInt (off after-zero) (signed32 current-sn)) ≡ zero8 →
        int32InBounds (addInt (signed32 current-sn) oneZ)
        ∧ ((next-sn : Word32) →
            signed32 next-sn ≡ addInt (signed32 current-sn) oneZ →
            uint32InBounds (addInt (unsignedZ done) oneZ)
            ∧ ((next-done : Word32) →
                unsignedZ next-done ≡ addInt (unsignedZ done) oneZ →
                (zeroZ ≤Z
                    subtractInt (unsignedZ (exp info)) (unsignedZ done)
                 ∧ subtractInt
                      (unsignedZ (exp info)) (unsignedZ next-done)
                    <Z subtractInt
                      (unsignedZ (exp info)) (unsignedZ done))
                ∧ PaddingInvariant total base info size original-sp
                    current-up n initial-sn next-done next-sn after-zero))))
    ((zeroZ ≤Z value previous-up (signed32 previous-n)
      ∧ value current-up (signed32 n)
          <Z value previous-up (signed32 previous-n))
     ∧ OuterInvariant total base info un size original-sp
          previous-up (addInt loop-index oneZ)
          current-up n current-sp current-sn)

AfterLimbBlock :
  {Zone : Set} →
  Int → Int → BaseInfo → Ptr Zone Word8 → Ptr Zone Word8 → Word32 →
  Word32 → Word64 → Word64 → Word64 →
  Ptr Zone Word64 → Word32 → Word32 → Word64 →
  Ptr Zone Word64 → Word32 → Int → Ptr Zone Word8 → Set
AfterLimbBlock {Zone} total base info original-sp before-sp size un shift d1 di
  current-up n initial-sn input previous-up previous-n loop-index spn =
  unsignedZ (exp info) ≤Z max32Z
  ∧ ((signed-exp : Word32) →
      signed32 signed-exp ≡ unsignedZ (exp info) →
      int32InBounds (addInt (signed32 signed-exp) oneZ)
      ∧ ((capacity : Word32) →
          signed32 capacity ≡ addInt (signed32 signed-exp) oneZ →
          ((twoZ ≤Z b info ∧ b info ≤Z twoFiftySixZ)
           ∧ writeable spn ≡ true
           ∧ euclideanDivide radixZ twoZ ≤Z unsignedZ d1
           ∧ (zeroZ ≤Z unsignedZ shift
              ∧ unsignedZ shift ≤Z sixtyThreeZ)
           ∧ multiplyInt (b info) (powerInt twoZ (unsignedZ shift))
                ≡ unsignedZ d1
           ∧ reciprocal di d1
           ∧ valid spn (signed32 capacity)
           ∧ zeroZ <Z signed32 capacity
           ∧ unsignedZ input <Z powerInt (b info) (signed32 capacity))
          ∧ ((after-local returned : Ptr Zone Word8) →
              FunctionEqual (pelts after-local) (pelts returned)
              ∧ sameFrame after-local spn →
              sameFrame returned before-sp →
              (done : Word32) →
              LimbDigitsPost (b info) spn after-local
                (signed32 capacity) input done →
              unsignedZ done ≤Z max32Z
              ∧ ((done-signed : Word32) →
                  signed32 done-signed ≡ unsignedZ done →
                  int32InBounds
                    (addInt (signed32 initial-sn) (signed32 done-signed))
                  ∧ ((new-sn : Word32) →
                      signed32 new-sn ≡
                        addInt
                          (signed32 initial-sn) (signed32 done-signed) →
                      PaddingInvariant total base info size original-sp
                        current-up n initial-sn done new-sn returned
                      ∧ ((loop-done current-sn : Word32)
                          (loop-sp : Ptr Zone Word8) →
                          sameFrame loop-sp returned →
                          PaddingInvariant total base info size original-sp
                            current-up n initial-sn loop-done current-sn
                            loop-sp →
                          PaddingStep total base info original-sp size un
                            current-up n initial-sn loop-done loop-sp
                            current-sn previous-up previous-n
                            loop-index))))))

OuterStep :
  {Zone : Set} →
  Int → Int → BaseInfo → Ptr Zone Word8 → Word32 →
  Ptr Zone Word64 → Word32 → Word64 → Word64 → Word64 →
  Ptr Zone Word64 → Ptr Zone Word64 → Word32 →
  Ptr Zone Word8 → Word32 → Int → Set
OuterStep {Zone} total base info original-sp size original-up un shift d1 di
  temporary current-up n current-sp sn loop-index =
  IfSet (intLess oneZ (signed32 n))
    ((valid current-up (signed32 n)
      ∧ valid temporary (signed32 n)
      ∧ writeable temporary ≡ true
      ∧ zeroZ <Z signed32 n
      ∧ zeroZ <Z unsignedZ (bb info))
     ∧ ((after-div : Ptr Zone Word64) →
        sameFrame after-div temporary →
        (remainder : Word64) →
        DivisionResult after-div current-up n (bb info) remainder →
        valid after-div (signed32 n)
        ∧ valid current-up (signed32 n)
        ∧ writeable current-up ≡ true
        ∧ ((copied : Ptr Zone Word64) →
            sameFrame copied current-up →
            mapEqSubShift (pelts copied) (pelts after-div)
              (off copied) (off after-div) (signed32 n)
            ∧ ((j : Int) →
                (j <Z off copied
                 ∨ addInt (off copied) (signed32 n) ≤Z j) →
                pelts copied j ≡ pelts current-up j) →
            int32InBounds (subtractInt (signed32 n) oneZ)
            ∧ ((n-minus-one : Word32) →
                signed32 n-minus-one ≡
                  subtractInt (signed32 n) oneZ →
                accessAt copied
                  (addInt (off copied) (signed32 n-minus-one))
                ∧ ((top : Word64) →
                    top ≡ pelts copied
                      (addInt (off copied) (signed32 n-minus-one)) →
                    (is-zero : Bool) →
                    (unsignedZ top ≡ zeroZ → is-zero ≡ true)
                    ∧ (is-zero ≡ true → top ≡ natToVec 64 0) →
                    (decrement : Word32) →
                    IfSet is-zero
                      (decrement ≡ one32) (decrement ≡ zero32) →
                    int32InBounds
                      (subtractInt (signed32 n) (signed32 decrement))
                    ∧ ((next-n : Word32) →
                        signed32 next-n ≡
                          subtractInt
                            (signed32 n) (signed32 decrement) →
                        (lo current-sp
                           ≤Z addInt (off current-sp) (signed32 sn)
                         ∧ addInt (off current-sp) (signed32 sn)
                            ≤Z hi current-sp)
                        ∧ ((spn : Ptr Zone Word8) →
                            shiftedPointer spn current-sp (signed32 sn) →
                            AfterLimbBlock total base info original-sp
                              current-sp size un shift d1 di copied next-n sn
                              remainder current-up n loop-index spn)))))))
    (PartialPost total base original-sp size current-up current-sp sn)

PartialBlock :
  {Zone : Set} →
  Int → Int → BaseInfo → Ptr Zone Word64 → Word32 →
  Ptr Zone Word8 → Word32 → Word64 → Word64 → Word64 → Set
PartialBlock {Zone} total base info original-up un original-sp size
  shift d1 di =
  IfSet (intLess oneZ (signed32 un))
    ((zeroZ ≤Z signed32 un)
     ∧ ((count : Word32) →
        unsignedZ count ≡ signed32 un →
        zeroZ ≤Z unsignedZ count
        ∧ ((temporary : Ptr Zone Word64) →
            allocated temporary (unsignedZ count) →
            OuterInvariant total base info un size original-sp original-up
              zeroZ original-up un original-sp zero32
            ∧ ((loop-index : Int)
                (loop-temporary loop-up : Ptr Zone Word64)
                (loop-n : Word32) (loop-sp : Ptr Zone Word8)
                (loop-sn : Word32) →
                sameFrame loop-temporary temporary →
                sameFrame loop-up original-up →
                sameFrame loop-sp original-sp →
                OuterInvariant total base info un size original-sp original-up
                  loop-index loop-up loop-n loop-sp loop-sn →
                OuterStep total base info original-sp size original-up
                  un shift d1 di loop-temporary loop-up loop-n loop-sp
                  loop-sn loop-index))))
    (PartialPost total base original-sp size original-up original-sp zero32)

Body :
  {Zone : Set} →
  Int → Ptr Zone Word64 → Word32 → Int → BaseInfo →
  Ptr Zone Word8 → Word32 → Word64 → Word64 → Word64 → Set
Body total original-up un base info original-sp size shift d1 di =
  PartialBlock total base info original-up un original-sp size shift d1 di
  ∧ FinalContinuation total base original-up un info original-sp size
      shift d1 di

Get-str-wmpn-get-str-other-statement : Set₁
Get-str-wmpn-get-str-other-statement =
  (Zone : Set) →
  (up : Ptr Zone Word64) →
  (un : Word32) →
  (base : Word32) →
  (info : BaseInfo) →
  (sp : Ptr Zone Word8) →
  (size : Word32) →
  valid up (signed32 un) →
  oneZ ≤Z signed32 un →
  b info ≡ signed32 base →
  writeable up ≡ true →
  writeable sp ≡ true →
  zeroZ <Z unsignedZ
    (pelts up
      (subtractInt (addInt (off up) (signed32 un)) oneZ)) →
  zeroZ <Z signed32 size →
  valid sp (signed32 size) →
  value up (signed32 un)
    <Z powerInt (signed32 base)
      (subtractInt (signed32 size) oneZ) →
  zeroZ ≤Z signed32 base
  ∧ ((base-limb : Word64) →
      unsignedZ base-limb ≡ signed32 base →
      zeroZ <Z unsignedZ base-limb
      ∧ ((count : Word32) →
          (multiplyInt
            (powerInt twoZ (signed32 count))
            (unsignedZ base-limb)
              ≤Z max64Z
           ∧ max64Z <Z multiplyInt twoZ
              (multiplyInt
                (powerInt twoZ (signed32 count))
                (unsignedZ base-limb))
           ∧ zeroZ ≤Z signed32 count
           ∧ signed32 count <Z sixtyFourZ) →
          zeroZ ≤Z signed32 count
          ∧ ((shift : Word64) →
              unsignedZ shift ≡ signed32 count →
              zeroZ ≤Z signed32 base
              ∧ ((base-limb-again : Word64) →
                  unsignedZ base-limb-again ≡ signed32 base →
                  ((zeroZ ≤Z unsignedZ shift
                    ∧ unsignedZ shift <Z sixtyFourZ)
                   ∧ multiplyInt
                        (powerInt twoZ (unsignedZ shift))
                        (unsignedZ base-limb-again)
                        ≤Z max64Z)
                  ∧ ((d1 : Word64) →
                      unsignedZ d1 ≡
                        multiplyInt
                          (powerInt twoZ (unsignedZ shift))
                          (unsignedZ base-limb-again) →
                      euclideanDivide radixZ twoZ ≤Z unsignedZ d1
                      ∧ ((di : Word64) →
                          reciprocal di d1 →
                          Body (value up (signed32 un)) up un
                            (signed32 base) info sp size shift d1 di))))))
