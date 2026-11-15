-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/add_Add_wmpn_addqtvc: the verification condition for
-- unequal-length multiprecision addition, including initial limb addition,
-- carry propagation, pointer aliasing, memory updates, and frame preservation.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module add_Add_wmpn_addqtvc where

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

modRadix : Nat → Nat
modRadix n with natLess n radixNat
... | true = n
... | false = subtractNat n radixNat

incrementModuloRadix : Word64 → Int
incrementModuloRadix limb =
  pos (modRadix (unsignedNat limb + 1))

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

accessAt :
  {Zone : Set} →
  Ptr Zone Word64 →
  Int →
  Set
accessAt p index =
  lo p ≤Z index ∧ index <Z hi p

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
  FunctionEq (pelts newer) (update (pelts older) index value)

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

carryBounds : Word64 → Set
carryBounds carry =
  zeroZ ≤Z unsignedZ carry
  ∧ unsignedZ carry ≤Z oneZ

zeroFlag : Word64 → Bool → Set
zeroFlag word flag =
  (unsignedZ word ≡ unsignedZ zero64 → flag ≡ true)
  ∧ (flag ≡ true → word ≡ zero64)

ySnapshot :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
ySnapshot newer common older =
  dataEq newer common
  ∧ cellCount common ≡ cellCount older
  ∧ off newer ≡ off older
  ∧ lo newer ≡ lo older
  ∧ hi newer ≡ hi older
  ∧ writeable newer ≡ writeable older
  ∧ region newer ≡ region older

xSnapshot :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
xSnapshot newer common older =
  dataEq newer common
  ∧ cellCount common ≡ cellCount older
  ∧ off newer ≡ off older
  ∧ lo newer ≡ lo older
  ∧ hi newer ≡ hi older
  ∧ writeable newer ≡ writeable older
  ∧ region newer ≡ region older

rSnapshot :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
rSnapshot newer older =
  cellCount newer ≡ cellCount older
  ∧ off newer ≡ off older
  ∧ lo newer ≡ lo older
  ∧ hi newer ≡ hi older
  ∧ writeable newer ≡ writeable older
  ∧ region newer ≡ region older

stateTransition :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
stateTransition newerY newerX newerR olderY olderX olderR =
  ySnapshot newerY newerR olderY
  ∧ xSnapshot newerX newerR olderX
  ∧ rSnapshot newerR olderR

valueEquation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Int →
  Int →
  Word64 →
  Set
valueEquation currentR originalX originalY size ySize carry =
  addInt
      (value currentR size)
      (multiplyInt
        (powerInt radixZ size)
        (unsignedZ carry))
    ≡ addInt
        (value originalX size)
        (value originalY ySize)

mapsPreserved :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Int →
  Int →
  Set
mapsPreserved currentR currentX currentY originalX originalY xSize ySize =
  (off currentR ≡ off currentX
   ∨ mapEqSub
       (pelts currentX)
       (pelts originalX)
       (off currentX)
       (addInt (off currentX) xSize))
  ∧
  (off currentR ≡ off currentY
   ∨ mapEqSub
       (pelts currentY)
       (pelts originalY)
       (off currentY)
       (addInt (off currentY) ySize))

loopInvariant :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Int →
  Set
loopInvariant sy sx originalR originalX originalY
  currentR currentX currentY i carry expected =
  (signed32 sy ≤Z signed32 i
   ∧ signed32 i ≤Z signed32 sx)
  ∧ (i ≡ sx ∨ unsignedZ carry ≡ expected)
  ∧ valueEquation
      currentR originalX originalY
      (signed32 i) (signed32 sy) carry
  ∧ outsideUnchanged currentR originalR (signed32 i)
  ∧ peltsEq currentX currentR
  ∧ peltsEq currentY currentR
  ∧ mapsPreserved
      currentR currentX currentY originalX originalY
      (signed32 sx) (signed32 sy)
  ∧ carryBounds carry

firstInvariant :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Set
firstInvariant sy sx originalR originalX originalY
  currentR currentX currentY i carry =
  loopInvariant sy sx originalR originalX originalY
    currentR currentX currentY i carry oneZ

secondInvariant :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Set
secondInvariant sy sx originalR originalX originalY
  currentR currentX currentY i carry =
  loopInvariant sy sx originalR originalX originalY
    currentR currentX currentY i carry zeroZ

finalPostcondition :
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
finalPostcondition sy sx originalR originalX originalY
  currentR currentX currentY carry =
  valueEquation
    currentR originalX originalY
    (signed32 sx) (signed32 sy) carry
  ∧ carryBounds carry
  ∧ outsideUnchanged currentR originalR (signed32 sx)
  ∧ mapsPreserved
      currentR currentX currentY originalX originalY
      (signed32 sx) (signed32 sy)

decreases :
  Word32 →
  Word32 →
  Word32 →
  Set
decreases sx current next =
  zeroZ ≤Z subtractInt (signed32 sx) (signed32 current)
  ∧ subtractInt (signed32 sx) (signed32 next)
      <Z subtractInt (signed32 sx) (signed32 current)

copyStep :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Set
copyStep sy sx originalR originalX originalY
  currentR currentX currentY i carry =
  accessAt currentX (addInt (off currentX) (signed32 i))
  ∧ accessAt originalX (addInt (off originalX) (signed32 i))
  ∧ (accessAt currentR (addInt (off currentR) (signed32 i))
     ∧ writeable currentR ≡ true)
  ∧
  ((nextY nextX nextR : Ptr _ Word64) →
    stateTransition
      nextY nextX nextR currentY currentX currentR →
    (mapUpdatedAt
       nextR currentR
       (addInt (off nextR) (signed32 i))
       (pelts currentX (addInt (off currentX) (signed32 i)))
     ∧ pelts nextR (addInt (off nextR) (signed32 i))
         ≡ pelts currentX (addInt (off currentX) (signed32 i))) →
    int32InBounds (addInt (signed32 i) oneZ)
    ∧
    ((nextI : Word32) →
      signed32 nextI ≡ addInt (signed32 i) oneZ →
      decreases sx i nextI
      ∧ secondInvariant
          sy sx originalR originalX originalY
          nextR nextX nextY nextI carry))

secondLoopStep :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Set
secondLoopStep sy sx originalR originalX originalY
  currentR currentX currentY i carry =
  IfSet
    (intLess (signed32 i) (signed32 sx))
    (copyStep sy sx originalR originalX originalY
      currentR currentX currentY i carry)
    (finalPostcondition sy sx originalR originalX originalY
      currentR currentX currentY carry)

allSecondLoopStates :
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
allSecondLoopStates sy sx originalR originalX originalY
  baseR baseX baseY carry =
  (i : Word32) →
  (currentY currentX currentR : Ptr _ Word64) →
  stateTransition currentY currentX currentR baseY baseX baseR →
  secondInvariant sy sx originalR originalX originalY
    currentR currentX currentY i carry →
  secondLoopStep sy sx originalR originalX originalY
    currentR currentX currentY i carry

secondLoopStart :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Set
secondLoopStart sy sx originalR originalX originalY
  currentR currentX currentY i carry =
  secondInvariant sy sx originalR originalX originalY
    currentR currentX currentY i carry
  ∧ allSecondLoopStates sy sx originalR originalX originalY
      currentR currentX currentY carry

afterIncrement :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word32 →
  Word64 →
  Bool →
  Set
afterIncrement sy sx originalR originalX originalY
  nextR nextX nextY previous carry nextI result flag =
  IfSet
    (notBool flag)
    (secondLoopStart sy sx originalR originalX originalY
      nextR nextX nextY nextI zero64)
    (decreases sx previous nextI
     ∧ firstInvariant sy sx originalR originalX originalY
         nextR nextX nextY nextI carry)

incrementWrite :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word64 →
  Set
incrementWrite sy sx originalR originalX originalY
  currentR currentX currentY i carry result =
  (accessAt currentR (addInt (off currentR) (signed32 i))
   ∧ writeable currentR ≡ true)
  ∧
  ((nextY nextX nextR : Ptr _ Word64) →
    stateTransition
      nextY nextX nextR currentY currentX currentR →
    (mapUpdatedAt
       nextR currentR
       (addInt (off nextR) (signed32 i))
       result
     ∧ pelts nextR (addInt (off nextR) (signed32 i)) ≡ result) →
    int32InBounds (addInt (signed32 i) oneZ)
    ∧
    ((nextI : Word32) →
      signed32 nextI ≡ addInt (signed32 i) oneZ →
      (flag : Bool) →
      zeroFlag result flag →
      afterIncrement sy sx originalR originalX originalY
        nextR nextX nextY i carry nextI result flag))

firstLoopBody :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Set
firstLoopBody sy sx originalR originalX originalY
  currentR currentX currentY i carry =
  accessAt currentX (addInt (off currentX) (signed32 i))
  ∧ accessAt originalX (addInt (off originalX) (signed32 i))
  ∧
  ((result : Word64) →
    unsignedZ result ≡
      incrementModuloRadix
        (pelts currentX (addInt (off currentX) (signed32 i))) →
    incrementWrite sy sx originalR originalX originalY
      currentR currentX currentY i carry result)

firstLoopStep :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Set
firstLoopStep sy sx originalR originalX originalY
  currentR currentX currentY i carry =
  IfSet
    (intLess (signed32 i) (signed32 sx))
    (firstLoopBody sy sx originalR originalX originalY
      currentR currentX currentY i carry)
    (finalPostcondition sy sx originalR originalX originalY
      currentR currentX currentY carry)

allFirstLoopStates :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
allFirstLoopStates sy sx originalR originalX originalY
  baseR baseX baseY =
  (i : Word32) →
  (carry : Word64) →
  (currentY currentX currentR : Ptr _ Word64) →
  stateTransition currentY currentX currentR baseY baseX baseR →
  firstInvariant sy sx originalR originalX originalY
    currentR currentX currentY i carry →
  firstLoopStep sy sx originalR originalX originalY
    currentR currentX currentY i carry

firstLoopStart :
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
firstLoopStart sy sx originalR originalX originalY
  currentR currentX currentY carry =
  firstInvariant sy sx originalR originalX originalY
    currentR currentX currentY sy carry
  ∧ allFirstLoopStates sy sx originalR originalX originalY
      currentR currentX currentY

afterInitialFlag :
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
  Bool →
  Set
afterInitialFlag sy sx originalR originalX originalY
  currentR currentX currentY carry flag =
  IfSet
    (notBool flag)
    (firstLoopStart sy sx originalR originalX originalY
      currentR currentX currentY carry)
    (secondLoopStart sy sx originalR originalX originalY
      currentR currentX currentY sy carry)

initialAdditionPostcondition :
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
initialAdditionPostcondition sy originalR originalX originalY
  currentR currentX currentY carry =
  valueEquation
    currentR originalX originalY
    (signed32 sy) (signed32 sy) carry
  ∧ carryBounds carry
  ∧ outsideUnchanged currentR originalR (signed32 sy)
  ∧ mapsPreserved
      currentR currentX currentY originalX originalY
      (signed32 sy) (signed32 sy)

afterInitialAddition :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
afterInitialAddition sy sx originalR originalX originalY
  currentR currentX currentY =
  (carry : Word64) →
  initialAdditionPostcondition
    sy originalR originalX originalY
    currentR currentX currentY carry →
  (flag : Bool) →
  zeroFlag carry flag →
  afterInitialFlag sy sx originalR originalX originalY
    currentR currentX currentY carry flag

allInitialStates :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
allInitialStates sy sx originalR originalX originalY =
  (currentY currentX currentR : Ptr _ Word64) →
  stateTransition
    currentY currentX currentR originalY originalX originalR →
  afterInitialAddition sy sx originalR originalX originalY
    currentR currentX currentY

wmpnAddConclusion :
  {Zone : Set} →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
wmpnAddConclusion sy sx r x y =
  zeroZ ≤Z signed32 sy
  ∧ valid r (signed32 sy)
  ∧ valid x (signed32 sy)
  ∧ valid y (signed32 sy)
  ∧ nonoverlap r (signed32 sy) x (signed32 sy)
  ∧ nonoverlap r (signed32 sy) y (signed32 sy)
  ∧ dataEq r x
  ∧ dataEq x y
  ∧ writeable r ≡ true
  ∧ allInitialStates sy sx r x y

wmpn-add'vc : Set₁
wmpn-add'vc =
  (Zone : Set) →
  (sy sx : Word32) →
  (r x y : Ptr Zone Word64) →
  zeroZ ≤Z signed32 sy →
  signed32 sy ≤Z signed32 sx →
  valid r (signed32 sx) →
  valid x (signed32 sx) →
  valid y (signed32 sy) →
  nonoverlap r (signed32 sx) x (signed32 sx) →
  nonoverlap r (signed32 sx) y (signed32 sy) →
  dataEq r x →
  dataEq x y →
  writeable r ≡ true →
  wmpnAddConclusion sy sx r x y
