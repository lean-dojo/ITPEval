-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/sub_Sub_sub_n_rxqtvc: the verification condition for
-- in-place equal-length multiprecision subtraction into the first operand,
-- including borrow arithmetic, pointer aliasing, memory framing, and metadata
-- preservation. This file contains no proof.

{-# OPTIONS --safe #-}

module sub_Sub_sub_n_rxqtvc where

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
  subtractInt (pos (unsignedNat bits)) (pos 4294967296)

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

viewMinEq :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
viewMinEq current original =
  off current ≡ off original
  ∧ lo current ≡ lo original
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
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word64 →
  Set
wmpnPostcondition size nr nx ny nr1 nx1 ny1 result =
  subtractInt
      (value nr1 (signed32 size))
      (multiplyInt
        (powerInt radixZ (signed32 size))
        (unsignedZ result))
    ≡ subtractInt
        (value nx (signed32 size))
        (value ny (signed32 size))
  ∧ (zeroZ ≤Z unsignedZ result
     ∧ unsignedZ result ≤Z oneZ)
  ∧ outsideUnchanged nr1 nr (signed32 size)
  ∧
    (off nr1 ≡ off nx1
     ∨ mapEqSub
         (pelts nx1)
         (pelts nx)
         (off nx1)
         (addInt (off nx1) (signed32 size)))
  ∧
    (off nr1 ≡ off ny1
     ∨ mapEqSub
         (pelts ny1)
         (pelts ny)
         (off ny1)
         (addInt (off ny1) (signed32 size)))

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
closePrecondition size x1 y1 nr1 nx1 ny1 m =
  (writeable x1 ≡ true ∧ writeable nr1 ≡ true)
  ∧ ok m ≡ true
  ∧ (zeroZ ≤Z signed32 size ∧ signed32 size ≤Z signed32 size)
  ∧ identical nr1 nx1
  ∧ orderedDisjoint nx1 (signed32 size) ny1 (signed32 size)
  ∧ (zx m ≡ region x1 ∧ zy m ≡ region y1)
  ∧ lx m ≡ size
  ∧ ly m ≡ size

finalPostcondition :
  {Zone : Set} →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word64 →
  Set
finalPostcondition size x y x2 y2 result =
  subtractInt
      (value x2 (signed32 size))
      (multiplyInt
        (powerInt radixZ (signed32 size))
        (unsignedZ result))
    ≡ subtractInt
        (value x (signed32 size))
        (value y (signed32 size))
  ∧ (zeroZ ≤Z unsignedZ result
     ∧ unsignedZ result ≤Z oneZ)
  ∧ outsideUnchanged x2 x (signed32 size)
  ∧ peltsEq y2 y
  ∧ value y2 (signed32 size) ≡ value y (signed32 size)
  ∧ (lo x2 ≡ lo x
     ∧ hi x2 ≡ hi x
     ∧ plength x2 ≡ plength x)
  ∧ lo y2 ≡ lo y
  ∧ hi y2 ≡ hi y
  ∧ plength y2 ≡ plength y

closeObligation :
  {Zone : Set} →
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
closeObligation size x y x1 y1 nx1 ny1 m result =
  (m1 : AliasMem _) →
  (ny2 nx2 y2 x2 : Ptr _ Word64) →
  sameAliasFields m1 m →
  viewEq ny2 ny1 →
  viewEq nx2 nx1 →
  viewMinEq y2 y1 →
  viewMinEq x2 x1 →
  ((hi x2 ≡ signed32 (mx m1)
    ∧ hi y2 ≡ signed32 (my m1))
   ∧ mapEqSubShift
       (pelts nx1) (pelts x2)
       (off nx2) (off x2) (signed32 size)
   ∧ mapEqSubShift
       (pelts ny1) (pelts y2)
       (off ny2) (off y2) (signed32 size)
   ∧ outsideUnchanged x2 x1 (signed32 size)
   ∧ outsideUnchanged y2 y1 (signed32 size)
   ∧ (plength x2 ≡ plength x1
      ∧ plength y2 ≡ plength y1)
   ∧ lo x2 ≡ lo x1
   ∧ lo y2 ≡ lo y1) →
  finalPostcondition size x y x2 y2 result

afterWmpnSub :
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
afterWmpnSub size x y x1 y1 nr nx ny m =
  (ny1 nx1 nr1 : Ptr _ Word64) →
  nySnapshot ny1 nr1 ny →
  nxSnapshot nx1 nr1 nx →
  nrSnapshot nr1 nr →
  (result : Word64) →
  wmpnPostcondition size nr nx ny nr1 nx1 ny1 result →
  closePrecondition size x1 y1 nr1 nx1 ny1 m
  ∧ closeObligation size x y x1 y1 nx1 ny1 m result

openedStateConclusion :
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
openedStateConclusion size x y y1 x1 nr nx ny m =
  (zeroZ ≤Z signed32 size
   ∧ (valid nr (signed32 size)
      ∧ valid nx (signed32 size)
      ∧ valid ny (signed32 size))
   ∧ nonoverlap nr (signed32 size) nx (signed32 size)
   ∧ nonoverlap nr (signed32 size) ny (signed32 size)
   ∧ (dataEq nr nx ∧ dataEq nx ny)
   ∧ writeable nr ≡ true)
  ∧ afterWmpnSub size x y x1 y1 nr nx ny m

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
openRxAntecedent size x y y1 x1 nr nx ny m =
  writeable nr ≡ true
  ∧ (value nx (signed32 size) ≡ value x (signed32 size)
     ∧ value ny (signed32 size) ≡ value y (signed32 size))
  ∧ (valid nx (signed32 size) ∧ valid ny (signed32 size))
  ∧ identical nr nx
  ∧ orderedDisjoint nx (signed32 size) ny (signed32 size)
  ∧ (zx m ≡ region x1 ∧ zy m ≡ region y1)
  ∧ (signed32 (mx m) ≡ hi x
     ∧ signed32 (my m) ≡ hi y)
  ∧ (lx m ≡ size ∧ ly m ≡ size)
  ∧ ok m ≡ true
  ∧ mapEqSubShift
      (pelts nx) (pelts x1)
      (off nx) (off x1) (signed32 size)
  ∧ mapEqSubShift
      (pelts ny) (pelts y1)
      (off ny) (off y1) (signed32 size)
  ∧ (peltsEq x1 x ∧ peltsEq y1 y)
  ∧ (plength x1 ≡ plength x ∧ plength y1 ≡ plength y)
  ∧ (lo x1 ≡ lo x ∧ lo y1 ≡ lo y)
  ∧ dataEq nr nx
  ∧ dataEq nx ny

allOpenedStates :
  {Zone : Set} →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
allOpenedStates size x y y1 x1 =
  (nr nx ny : Ptr _ Word64) →
  (m : AliasMem _) →
  openRxAntecedent size x y y1 x1 nr nx ny m →
  openedStateConclusion size x y y1 x1 nr nx ny m

allViews :
  {Zone : Set} →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
allViews size x y =
  (y1 x1 : Ptr _ Word64) →
  viewEq y1 y →
  viewEq x1 x →
  allOpenedStates size x y y1 x1

subNRxConclusion :
  {Zone : Set} →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
subNRxConclusion size x y =
  valid x (signed32 size)
  ∧ valid y (signed32 size)
  ∧ zeroZ ≤Z signed32 size
  ∧ signed32 size ≤Z signed32 size
  ∧ writeable x ≡ true
  ∧ allViews size x y

sub-n-rx'vc : Set₁
sub-n-rx'vc =
  (Zone : Set) →
  (size : Word32) →
  (x y : Ptr Zone Word64) →
  zeroZ ≤Z signed32 size →
  valid x (signed32 size) →
  valid y (signed32 size) →
  writeable x ≡ true →
  subNRxConclusion size x y
