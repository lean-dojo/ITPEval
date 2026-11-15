-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/add_Add_add_ryqtvc: the verification condition for
-- possibly unequal-length multiprecision addition into the second operand,
-- including alias separation, carry bounds, value preservation, and memory
-- framing.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module add_Add_add_ryqtvc where

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

zeroZ oneZ radixZ : Int
zeroZ = pos 0
oneZ = pos 1
radixZ = pos 18446744073709551616

min32 max32 : Int
min32 = negsuc 2147483647
max32 = pos 2147483647

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
  addInt (pos (unsignedNat bits)) (negsuc 4294967295)

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

FunctionEq :
  {A B : Set} →
  (A → B) →
  (A → B) →
  Set
FunctionEq f g = (x : _) → f x ≡ g x

peltsEq :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
peltsEq p q = FunctionEq (pelts p) (pelts q)

dataEq :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
dataEq p q =
  cellCount p ≡ cellCount q
  ∧ peltsEq p q

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

mapEqSub :
  (Int → Word64) →
  (Int → Word64) →
  Int →
  Int →
  Set
mapEqSub firstMap secondMap lower upper =
  (i : Int) →
  (lower ≤Z i ∧ i <Z upper) →
  firstMap i ≡ secondMap i

mapEqSubShift :
  (Int → Word64) →
  (Int → Word64) →
  Int →
  Int →
  Int →
  Set
mapEqSubShift firstMap secondMap firstOffset secondOffset size =
  (i : Int) →
  (zeroZ ≤Z i ∧ i <Z size) →
  firstMap (addInt firstOffset i)
    ≡ secondMap (addInt secondOffset i)

record AliasMem (Zone : Set) : Set where
  constructor aliasMemory
  field
    zr : Zone
    zx : Zone
    zy : Zone
    mr : Word32
    mx : Word32
    my : Word32
    lr : Word32
    lx : Word32
    ly : Word32
    ok : Bool

open AliasMem public

identical :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
identical firstPtr secondPtr =
  dataEq firstPtr secondPtr
  ∧ off firstPtr ≡ off secondPtr
  ∧ lo firstPtr ≡ lo secondPtr
  ∧ hi firstPtr ≡ hi secondPtr
  ∧ region firstPtr ≡ region secondPtr

viewEq :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
viewEq current original =
  off current ≡ off original
  ∧ writeable current ≡ writeable original
  ∧ region current ≡ region original

nonoverlap :
  {Zone : Set} →
  Ptr Zone Word64 →
  Int →
  Ptr Zone Word64 →
  Int →
  Set
nonoverlap firstPtr firstSize secondPtr secondSize =
  off firstPtr ≡ off secondPtr
  ∨ addInt (off firstPtr) firstSize ≤Z off secondPtr
  ∨ addInt (off secondPtr) secondSize ≤Z off firstPtr

orderedDisjoint :
  {Zone : Set} →
  Ptr Zone Word64 →
  Int →
  Ptr Zone Word64 →
  Int →
  Set
orderedDisjoint firstPtr firstSize secondPtr secondSize =
  (zeroZ ≤Z off firstPtr
   ∧ addInt (off firstPtr) firstSize ≤Z off secondPtr)
  ∨
  (zeroZ ≤Z off secondPtr
   ∧ addInt (off secondPtr) secondSize ≤Z off firstPtr)

outsideUnchanged :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Int →
  Set
outsideUnchanged current original size =
  (j : Int) →
  (j <Z off current
   ∨ addInt (off current) size ≤Z j) →
  pelts current j ≡ pelts original j

sameAliasFields :
  {Zone : Set} →
  AliasMem Zone →
  AliasMem Zone →
  Set
sameAliasFields current original =
  zr current ≡ zr original
  ∧ zx current ≡ zx original
  ∧ zy current ≡ zy original
  ∧ mr current ≡ mr original
  ∧ mx current ≡ mx original
  ∧ my current ≡ my original
  ∧ lr current ≡ lr original
  ∧ lx current ≡ lx original
  ∧ ly current ≡ ly original

nxSnapshot :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
nxSnapshot nx1 nr1 nx =
  dataEq nx1 nr1
  ∧ cellCount nr1 ≡ cellCount nx
  ∧ off nx1 ≡ off nx
  ∧ lo nx1 ≡ lo nx
  ∧ hi nx1 ≡ hi nx
  ∧ writeable nx1 ≡ writeable nx
  ∧ region nx1 ≡ region nx

nySnapshot :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
nySnapshot ny1 nr1 ny =
  dataEq ny1 nr1
  ∧ cellCount nr1 ≡ cellCount ny
  ∧ off ny1 ≡ off ny
  ∧ lo ny1 ≡ lo ny
  ∧ hi ny1 ≡ hi ny
  ∧ writeable ny1 ≡ writeable ny
  ∧ region ny1 ≡ region ny

nrSnapshot :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
nrSnapshot nr1 nr =
  cellCount nr1 ≡ cellCount nr
  ∧ off nr1 ≡ off nr
  ∧ lo nr1 ≡ lo nr
  ∧ hi nr1 ≡ hi nr
  ∧ writeable nr1 ≡ writeable nr
  ∧ region nr1 ≡ region nr

wmpnPostcondition :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word64 →
  Set
wmpnPostcondition sy sx nr nx ny nr1 nx1 ny1 result =
  addInt
      (value nr1 (signed32 sx))
      (multiplyInt
        (powerInt radixZ (signed32 sx))
        (unsignedZ result))
    ≡ addInt
        (value nx (signed32 sx))
        (value ny (signed32 sy))
  ∧ (zeroZ ≤Z unsignedZ result
     ∧ unsignedZ result ≤Z oneZ)
  ∧ outsideUnchanged nr1 nr (signed32 sx)
  ∧
    (off nr1 ≡ off nx1
     ∨ mapEqSub
         (pelts nx1)
         (pelts nx)
         (off nx1)
         (addInt (off nx1) (signed32 sx)))
  ∧
    (off nr1 ≡ off ny1
     ∨ mapEqSub
         (pelts ny1)
         (pelts ny)
         (off ny1)
         (addInt (off ny1) (signed32 sy)))

closePrecondition :
  {Zone : Set} →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  AliasMem Zone →
  Set
closePrecondition sx y1 x1 nr1 ny1 nx1 m =
  (writeable y1 ≡ true ∧ writeable nr1 ≡ true)
  ∧ ok m ≡ true
  ∧ (zeroZ ≤Z signed32 sx ∧ signed32 sx ≤Z signed32 sx)
  ∧ identical nr1 ny1
  ∧ orderedDisjoint ny1 (signed32 sx) nx1 (signed32 sx)
  ∧ (zx m ≡ region y1 ∧ zy m ≡ region x1)
  ∧ lx m ≡ sx
  ∧ ly m ≡ sx

finalPostcondition :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word64 →
  Set
finalPostcondition sy sx x y x2 y2 result =
  addInt
      (value y2 (signed32 sx))
      (multiplyInt
        (powerInt radixZ (signed32 sx))
        (unsignedZ result))
    ≡ addInt
        (value x (signed32 sx))
        (value y (signed32 sy))
  ∧ (zeroZ ≤Z unsignedZ result
     ∧ unsignedZ result ≤Z oneZ)
  ∧ outsideUnchanged y2 y (signed32 sx)
  ∧ peltsEq x2 x
  ∧ value x2 (signed32 sx) ≡ value x (signed32 sx)
  ∧ (lo x2 ≡ lo x ∧ hi x2 ≡ hi x
     ∧ plength x2 ≡ plength x)
  ∧ lo y2 ≡ lo y
  ∧ hi y2 ≡ hi y
  ∧ plength y2 ≡ plength y

closeObligation :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  AliasMem Zone →
  Word64 →
  Set
closeObligation sy sx x y x1 y1 nx1 ny1 m result =
  (m1 : AliasMem _) →
  (nx2 ny2 y2 x2 : Ptr _ Word64) →
  sameAliasFields m1 m →
  viewEq nx2 nx1 →
  viewEq ny2 ny1 →
  (off y2 ≡ off y1
   ∧ lo y2 ≡ lo y1
   ∧ writeable y2 ≡ writeable y1
   ∧ region y2 ≡ region y1) →
  (off x2 ≡ off x1
   ∧ lo x2 ≡ lo x1
   ∧ writeable x2 ≡ writeable x1
   ∧ region x2 ≡ region x1) →
  ((hi y2 ≡ signed32 (mx m1)
    ∧ hi x2 ≡ signed32 (my m1))
   ∧ mapEqSubShift
       (pelts ny1) (pelts y2)
       (off ny2) (off y2) (signed32 sx)
   ∧ mapEqSubShift
       (pelts nx1) (pelts x2)
       (off nx2) (off x2) (signed32 sx)
   ∧ outsideUnchanged y2 y1 (signed32 sx)
   ∧ outsideUnchanged x2 x1 (signed32 sx)
   ∧ (plength y2 ≡ plength y1
      ∧ plength x2 ≡ plength x1)
   ∧ lo y2 ≡ lo y1
   ∧ lo x2 ≡ lo x1) →
  finalPostcondition sy sx x y x2 y2 result

afterWmpnAdd :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  AliasMem Zone →
  Set
afterWmpnAdd sy sx x y x1 y1 nr nx ny m =
  (nx1 ny1 nr1 : Ptr _ Word64) →
  nxSnapshot nx1 nr1 nx →
  nySnapshot ny1 nr1 ny →
  nrSnapshot nr1 nr →
  (result : Word64) →
  wmpnPostcondition sy sx nr nx ny nr1 nx1 ny1 result →
  closePrecondition sx y1 x1 nr1 ny1 nx1 m
  ∧ closeObligation sy sx x y x1 y1 nx1 ny1 m result

openedStateConclusion :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  AliasMem Zone →
  Set
openedStateConclusion sy sx x y y1 x1 nr ny nx m =
  ((zeroZ ≤Z signed32 sy
    ∧ signed32 sy ≤Z signed32 sx)
   ∧ (valid nr (signed32 sx)
      ∧ valid nx (signed32 sx)
      ∧ valid ny (signed32 sy))
   ∧ nonoverlap nr (signed32 sx) nx (signed32 sx)
   ∧ nonoverlap nr (signed32 sx) ny (signed32 sy)
   ∧ (dataEq nr nx ∧ dataEq nx ny)
   ∧ writeable nr ≡ true)
  ∧ afterWmpnAdd sy sx x y x1 y1 nr nx ny m

openRxAntecedent :
  {Zone : Set} →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  AliasMem Zone →
  Set
openRxAntecedent sx x y y1 x1 nr ny nx m =
  writeable nr ≡ true
  ∧ (value ny (signed32 sx) ≡ value y (signed32 sx)
     ∧ value nx (signed32 sx) ≡ value x (signed32 sx))
  ∧ (valid ny (signed32 sx) ∧ valid nx (signed32 sx))
  ∧ identical nr ny
  ∧ orderedDisjoint ny (signed32 sx) nx (signed32 sx)
  ∧ (zx m ≡ region y1 ∧ zy m ≡ region x1)
  ∧ (signed32 (mx m) ≡ hi y
     ∧ signed32 (my m) ≡ hi x)
  ∧ (lx m ≡ sx ∧ ly m ≡ sx)
  ∧ ok m ≡ true
  ∧ mapEqSubShift
      (pelts ny) (pelts y1)
      (off ny) (off y1) (signed32 sx)
  ∧ mapEqSubShift
      (pelts nx) (pelts x1)
      (off nx) (off x1) (signed32 sx)
  ∧ (peltsEq y1 y ∧ peltsEq x1 x)
  ∧ (plength y1 ≡ plength y ∧ plength x1 ≡ plength x)
  ∧ (lo y1 ≡ lo y ∧ lo x1 ≡ lo x)
  ∧ dataEq nr ny
  ∧ dataEq ny nx

allOpenedStates :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
allOpenedStates sy sx x y y1 x1 =
  (nr ny nx : Ptr _ Word64) →
  (m : AliasMem _) →
  openRxAntecedent sx x y y1 x1 nr ny nx m →
  openedStateConclusion sy sx x y y1 x1 nr ny nx m

allViews :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
allViews sy sx x y =
  (y1 x1 : Ptr _ Word64) →
  viewEq y1 y →
  viewEq x1 x →
  allOpenedStates sy sx x y y1 x1

addRyConclusion :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
addRyConclusion sy sx x y =
  valid y (signed32 sx)
  ∧ valid x (signed32 sx)
  ∧ zeroZ ≤Z signed32 sx
  ∧ signed32 sx ≤Z signed32 sx
  ∧ writeable y ≡ true
  ∧ allViews sy sx x y

add-ry'vc : Set₁
add-ry'vc =
  (Zone : Set) →
  (sy sx : Word32) →
  (x y : Ptr Zone Word64) →
  zeroZ ≤Z signed32 sy →
  signed32 sy ≤Z signed32 sx →
  valid x (signed32 sx) →
  valid y (signed32 sx) →
  writeable y ≡ true →
  addRyConclusion sy sx x y
