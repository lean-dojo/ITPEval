-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/powm_Powm_redcifyqtvc: the verification condition for
-- radix-based reduction of a multiprecision value by zero-padding, copying,
-- and quotient-remainder division, with pointer-frame and modular-result
-- obligations. This file contains no proof.

{-# OPTIONS --safe #-}

module powm_Powm_redcifyqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
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

-- Why3 Euclidean remainder for the positive moduli occurring in this VC.
euclideanModuloPositive : Int → Nat → Int
euclideanModuloPositive _ zero = pos zero
euclideanModuloPositive (pos n) d@(suc _) =
  pos (natModulo n d)
euclideanModuloPositive (negsuc n) d@(suc _) with natModulo (suc n) d
... | zero = pos zero
... | r@(suc _) = pos (d - r)

moduloInt : Int → Int → Int
moduloInt dividend modulus =
  euclideanModuloPositive dividend (intToNat modulus)

powerNat : Nat → Nat → Nat
powerNat base zero = 1
powerNat base (suc exponent) =
  base * powerNat base exponent

powerZ : Nat → Int → Int
powerZ base exponent =
  pos (powerNat base (intToNat exponent))

data Vec (A : Set) : Nat → Set where
  []V   : Vec A zero
  _∷V_  : {n : Nat} → A → Vec A n → Vec A (suc n)

replicateVec : {A : Set} → (n : Nat) → A → Vec A n
replicateVec zero value = []V
replicateVec (suc n) value =
  value ∷V replicateVec n value

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

signed32 : Word32 → Int
signed32 bits with lastBit bits
... | false = unsignedZ bits
... | true =
  subtractInt (unsignedZ bits) (pos 4294967296)

zero64 : Word64
zero64 = replicateVec 64 false

zeroZ oneZ max32Z radixZ : Int
zeroZ = pos 0
oneZ = pos 1
max32Z = pos 2147483647
radixZ = pos 18446744073709551616

min32Z : Int
min32Z = negsuc 2147483647

radixNat : Nat
radixNat = 18446744073709551616

int32InBounds : Int → Set
int32InBounds value =
  min32Z ≤Z value ∧ value ≤Z max32Z

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

PeltsEqual :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Set
PeltsEqual p q =
  (index : Int) → pelts p index ≡ pelts q index

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
  first (addInt firstOffset i) ≡
    second (addInt secondOffset i)

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

redc : Int → Int → Int → Int → Set
redc reduced original limb-count modulus =
  moduloInt reduced modulus ≡
    moduloInt
      (multiplyInt
        (powerZ radixNat limb-count)
        original)
      modulus

allocationFrame :
  {Zone : Set} →
  Ptr Zone →
  Int →
  Set
allocationFrame p size =
  plength p ≡ size
  ∧ off p ≡ zeroZ
  ∧ lo p ≡ zeroZ
  ∧ hi p ≡ size
  ∧ writeable p ≡ true

sameFrame :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Set
sameFrame newer older =
  listLength (contents newer) ≡ listLength (contents older)
  ∧ off newer ≡ off older
  ∧ lo newer ≡ lo older
  ∧ hi newer ≡ hi older
  ∧ writeable newer ≡ writeable older
  ∧ region newer ≡ region older

outsideUnchanged :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Int →
  Set
outsideUnchanged current original size =
  (j : Int) →
  (j <Z off current ∨ addInt (off current) size ≤Z j) →
  pelts current j ≡ pelts original j

shiftedState :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Int →
  Set
shiftedState shifted original displacement =
  off shifted ≡ addInt (off original) displacement
  ∧ plength shifted ≡ plength original
  ∧ PeltsEqual shifted original
  ∧ contents shifted ≡ contents original
  ∧ lo shifted ≡ lo original
  ∧ hi shifted ≡ hi original
  ∧ region shifted ≡ region original
  ∧ writeable shifted ≡ writeable original

copyResultFrame :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Set
copyResultFrame copied destination shifted =
  contents copied ≡ contents destination
  ∧ listLength (contents destination) ≡
      listLength (contents shifted)
  ∧ off copied ≡ off shifted
  ∧ lo copied ≡ lo shifted
  ∧ hi copied ≡ hi shifted
  ∧ writeable copied ≡ writeable shifted
  ∧ region copied ≡ region shifted

finalDivisionPremise :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word32 →
  Set
finalDivisionPremise tp2 qp1 mp rp1 o7 n =
  value tp2 (signed32 o7) ≡
    addInt
      (multiplyInt
        (value qp1
          (addInt
            (subtractInt (signed32 o7) (signed32 n))
            oneZ))
        (value mp (signed32 n)))
      (value rp1 (signed32 n))
  ∧ value rp1 (signed32 n) <Z value mp (signed32 n)

finalResult :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word32 →
  Ptr Zone →
  Set
finalResult rp1 up un n mp =
  value rp1 (signed32 n) ≡
    moduloInt
      (multiplyInt
        (powerZ radixNat (signed32 n))
        (value up (signed32 un)))
      (value mp (signed32 n))
  ∧ redc
      (value rp1 (signed32 n))
      (value up (signed32 un))
      (signed32 n)
      (value mp (signed32 n))

afterFinalPointers :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Ptr Zone →
  Word32 →
  Word32 →
  Set
afterFinalPointers qp rp tp2 mp o7 up un n =
  (qp1 rp1 : Ptr _) →
  sameFrame qp1 qp →
  sameFrame rp1 rp →
  finalDivisionPremise tp2 qp1 mp rp1 o7 n →
  finalResult rp1 up un n mp

divisionFacts :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Set
divisionFacts tp2 mp qp rp up o7 n un =
  (oneZ ≤Z signed32 n
   ∧ signed32 n ≤Z signed32 o7
   ∧ signed32 o7 ≤Z subtractInt max32Z oneZ)
  ∧ valid tp2 (signed32 o7)
  ∧ valid mp (signed32 n)
  ∧ valid qp
      (addInt
        (subtractInt (signed32 o7) (signed32 n))
        oneZ)
  ∧ valid rp (signed32 n)
  ∧ (writeable qp ≡ true ∧ writeable rp ≡ true)
  ∧ zeroZ <Z
      unsignedZ
        (pelts mp
          (subtractInt
            (addInt (off mp) (signed32 n))
            oneZ))
  ∧ afterFinalPointers qp rp tp2 mp o7 up un n

afterO7 :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word32 →
  Set
afterO7 tp2 mp qp rp up n un =
  (o7 : Word32) →
  signed32 o7 ≡ addInt (signed32 un) (signed32 n) →
  divisionFacts tp2 mp qp rp up o7 n un

afterCopy :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word32 →
  Set
afterCopy o5 tp1 up mp qp rp n un =
  (o6 tp2 : Ptr _) →
  copyResultFrame o6 tp2 o5 →
  sameFrame tp2 tp1 →
  (mapEqSubShift
      (pelts o6)
      (pelts up)
      (off o6)
      (off up)
      (signed32 un)
   ∧ outsideUnchanged o6 o5 (signed32 un)) →
  int32InBounds (addInt (signed32 un) (signed32 n))
  ∧ afterO7 tp2 mp qp rp up n un

afterO5 :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word32 →
  Set
afterO5 tp1 up mp qp rp n un =
  (o5 : Ptr _) →
  shiftedState o5 tp1 (signed32 n) →
  (valid up (signed32 un)
   ∧ valid o5 (signed32 un)
   ∧ writeable o5 ≡ true)
  ∧ afterCopy o5 tp1 up mp qp rp n un

afterTp1 :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word32 →
  Set
afterTp1 tp up mp qp rp n un =
  (tp1 : Ptr _) →
  sameFrame tp1 tp →
  (value tp1 (signed32 n) ≡ zeroZ
   ∧ outsideUnchanged tp1 tp (signed32 n)) →
  (lo tp1 ≤Z addInt (off tp1) (signed32 n)
   ∧ addInt (off tp1) (signed32 n) ≤Z hi tp1)
  ∧ afterO5 tp1 up mp qp rp n un

afterQp :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Set
afterQp tp up mp rp n un o4 =
  (qp : Ptr _) →
  allocationFrame qp (unsignedZ o4) →
  (valid tp (signed32 n) ∧ writeable tp ≡ true)
  ∧ afterTp1 tp up mp qp rp n un

afterO4 :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Set
afterO4 tp up mp rp n un o3 =
  (o4 : Word32) →
  unsignedZ o4 ≡ signed32 o3 →
  zeroZ ≤Z unsignedZ o4
  ∧ afterQp tp up mp rp n un o4

afterO3 :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word32 →
  Set
afterO3 tp up mp rp n un =
  (o3 : Word32) →
  signed32 o3 ≡ addInt (signed32 un) oneZ →
  zeroZ ≤Z signed32 o3
  ∧ afterO4 tp up mp rp n un o3

afterTp :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Set
afterTp up mp rp n un o2 =
  (tp : Ptr _) →
  allocationFrame tp (unsignedZ o2) →
  int32InBounds (addInt (signed32 un) oneZ)
  ∧ afterO3 tp up mp rp n un

afterO2 :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word32 →
  Word32 →
  Set
afterO2 up mp rp n un o1 =
  (o2 : Word32) →
  unsignedZ o2 ≡ signed32 o1 →
  zeroZ ≤Z unsignedZ o2
  ∧ afterTp up mp rp n un o2

afterO1 :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word32 →
  Set
afterO1 up mp rp n un =
  (o1 : Word32) →
  signed32 o1 ≡ addInt (signed32 un) (signed32 n) →
  zeroZ ≤Z signed32 o1
  ∧ afterO2 up mp rp n un o1

redcify'vc : Set₁
redcify'vc =
  (Zone : Set) →
  (rp : Ptr Zone) →
  (n : Word32) →
  (up : Ptr Zone) →
  (un : Word32) →
  (mp : Ptr Zone) →
  valid rp (signed32 n) →
  valid up (signed32 un) →
  valid mp (signed32 n) →
  oneZ ≤Z signed32 n →
  oneZ ≤Z signed32 un →
  addInt (signed32 un) (signed32 n) <Z max32Z →
  zeroZ <Z
    unsignedZ
      (pelts mp
        (subtractInt
          (addInt (off mp) (signed32 n))
          oneZ)) →
  writeable rp ≡ true →
  int32InBounds (addInt (signed32 un) (signed32 n))
  ∧ afterO1 up mp rp n un
