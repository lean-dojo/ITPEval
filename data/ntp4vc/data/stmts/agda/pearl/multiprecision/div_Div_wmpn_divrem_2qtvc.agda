-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/div_Div_wmpn_divrem_2qtvc: the verification condition
-- for normalized two-limb multiprecision division, including reciprocal
-- estimation, initial adjustment, loop-invariant preservation, quotient
-- writes, and final remainder storage. This file contains no proof.

{-# OPTIONS --safe #-}

module div_Div_wmpn_divrem_2qtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; div-helper)

infix 4 _≤Z_ _<Z_
infixr 5 _∷V_
infixr 3 _∧_

data ⊥ : Set where

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

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

powerNat : Int → Nat → Int
powerNat base zero = pos 1
powerNat base (suc exponent) =
  multiplyInt base (powerNat base exponent)

powerInt : Int → Int → Int
powerInt base exponent = powerNat base (intToNat exponent)

natDivide : Nat → Nat → Nat
natDivide n zero = zero
natDivide n (suc m) = div-helper zero m n m

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

Word32 Word64 : Set
Word32 = Vec Bool 32
Word64 = Vec Bool 64

signed32 : Word32 → Int
signed32 bits with lastBit bits
... | false = pos (unsignedNat bits)
... | true =
  subtractInt (pos (unsignedNat bits)) (pos 4294967296)

zero64 one64 : Word64
zero64 = natToVec 64 0
one64 = natToVec 64 1

negativeOneZ zeroZ oneZ twoZ : Int
negativeOneZ = negsuc 0
zeroZ = pos 0
oneZ = pos 1
twoZ = pos 2

min32 max32 radixZ halfRadixZ : Int
min32 = negsuc 2147483647
max32 = pos 2147483647
radixZ = pos 18446744073709551616
halfRadixZ = pos 9223372036854775808

radixNat reciprocal3NumeratorNat : Nat
radixNat = 18446744073709551616
reciprocal3NumeratorNat =
  radixNat * radixNat * radixNat - 1

int32InBounds : Int → Set
int32InBounds n = min32 ≤Z n ∧ n ≤Z max32

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

valid : {Zone : Set} → Ptr Zone Word64 → Int → Set
valid p size =
  int32InBounds size
  ∧ zeroZ ≤Z size
  ∧ (zeroZ ≤Z lo p ∧ lo p ≤Z off p)
  ∧ addInt (off p) size ≤Z hi p
  ∧ hi p ≤Z plength p

accessAt : {Zone : Set} → Ptr Zone Word64 → Int → Set
accessAt p index = lo p ≤Z index ∧ index <Z hi p

cursorAt : {Zone : Set} → Ptr Zone Word64 → Int → Set
cursorAt p index = lo p ≤Z index ∧ index ≤Z hi p

FunctionEqual :
  {A B : Set} → (A → B) → (A → B) → Set
FunctionEqual f g = (x : _) → f x ≡ g x

sameShape :
  {Zone : Set} → Ptr Zone Word64 → Ptr Zone Word64 → Set
sameShape newer older =
  cellCount newer ≡ cellCount older
  ∧ off newer ≡ off older
  ∧ lo newer ≡ lo older
  ∧ hi newer ≡ hi older
  ∧ writeable newer ≡ writeable older
  ∧ region newer ≡ region older

shiftedBy :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 → Int → Set
shiftedBy shifted base amount =
  off shifted ≡ addInt (off base) amount
  ∧ plength shifted ≡ plength base
  ∧ FunctionEqual (pelts shifted) (pelts base)
  ∧ cellCount shifted ≡ cellCount base
  ∧ lo shifted ≡ lo base
  ∧ hi shifted ≡ hi base
  ∧ region shifted ≡ region base
  ∧ writeable shifted ≡ writeable base

update :
  {A : Set} → (Int → A) → Int → A → Int → A
update f index value query with intEqual query index
... | true = value
... | false = f query

updatedAt :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 → Int → Word64 → Set
updatedAt newer older index limb =
  FunctionEqual (pelts newer) (update (pelts older) index limb)
  ∧ pelts newer index ≡ limb

valueMapFrom : (Int → Word64) → Int → Nat → Int
valueMapFrom m index zero = zeroZ
valueMapFrom m index (suc count) =
  addInt
    (unsignedZ (m index))
    (multiplyInt
      radixZ
      (valueMapFrom m (addInt index oneZ) count))

valueSub : (Int → Word64) → Int → Int → Int
valueSub m lower upper =
  valueMapFrom m lower (intToNat (subtractInt upper lower))

value : {Zone : Set} → Ptr Zone Word64 → Int → Int
value p size =
  valueSub (pelts p) (off p) (addInt (off p) size)

reciprocal3by2 : Word64 → Word64 → Word64 → Set
reciprocal3by2 v dh dl =
  unsignedZ v ≡
  subtractInt
    (pos
      (natDivide reciprocal3NumeratorNat
        (unsignedNat dl + radixNat * unsignedNat dh)))
    radixZ

wordLessOrEqual : Word64 → Word64 → Bool
wordLessOrEqual x y =
  natLessOrEqual (unsignedNat x) (unsignedNat y)

wordLess : Word64 → Word64 → Bool
wordLess x y = natLess (unsignedNat x) (unsignedNat y)

adjustTest : Word64 → Word64 → Word64 → Word64 → Bool
adjustTest dh dl high low with wordLessOrEqual dh high
... | false = false
... | true with wordLess dh high
...   | true = true
...   | false = wordLessOrEqual dl low

remainderBound :
  Word64 → Word64 → Word64 → Word64 → Set
remainderBound low high dl dh =
  addInt (unsignedZ low) (multiplyInt radixZ (unsignedZ high))
  <Z
  addInt (unsignedZ dl) (multiplyInt radixZ (unsignedZ dh))

loopState :
  {Zone : Set} →
  Word32 → Ptr Zone Word64 → Ptr Zone Word64 →
  Ptr Zone Word64 → Word64 → Word64 → Word64 →
  Ptr Zone Word64 → Int → Set
loopState sx x y qState qh low high work index =
  (zeroZ ≤Z index
   ∧ index ≤Z subtractInt (signed32 sx) twoZ)
  ∧ off work ≡ addInt (off x) index
  ∧ plength work ≡ plength x
  ∧ lo work ≡ lo x
  ∧ hi work ≡ hi x
  ∧ FunctionEqual (pelts work) (pelts x)
  ∧ writeable work ≡ true
  ∧ value x (signed32 sx)
    ≡ addInt
        (addInt
          (multiplyInt
            (multiplyInt
              (addInt
                (valueSub
                  (pelts qState)
                  (addInt (off qState) index)
                  (subtractInt
                    (addInt (off qState) (signed32 sx))
                    twoZ))
                (multiplyInt
                  (unsignedZ qh)
                  (powerInt radixZ
                    (subtractInt
                      (subtractInt (signed32 sx) twoZ)
                      index))))
              (value y twoZ))
            (powerInt radixZ index))
          (value x index))
        (multiplyInt
          (powerInt radixZ index)
          (addInt
            (unsignedZ low)
            (multiplyInt radixZ (unsignedZ high))))
  ∧ remainderBound low high
      (pelts y (off y))
      (pelts y (addInt (off y) oneZ))

borrowResults :
  Word64 → Word64 → Word64 → Word64 → Set
borrowResults low dl result borrow =
  subtractInt
    (unsignedZ result)
    (multiplyInt radixZ (unsignedZ borrow))
    ≡ subtractInt
        (subtractInt (unsignedZ low) (unsignedZ dl))
        zeroZ
  ∧ zeroZ ≤Z unsignedZ borrow
  ∧ unsignedZ borrow ≤Z oneZ

allBorrowResults : Word64 → Word64 → Set
allBorrowResults low dl =
  (result borrow : Word64) →
  borrowResults low dl result borrow →
  zeroZ ≤Z unsignedZ borrow
  ∧ unsignedZ borrow ≤Z oneZ

initialAdjustWitness :
  Word64 → Word64 → Word64 →
  Word64 → Word64 → Word64 → Word64 → Set
initialAdjustWitness high low qh dh dl oldHigh oldLow =
  Exists Bool
    (λ selected →
      selected ≡ adjustTest dh dl oldHigh oldLow
      ∧
      IfSet
        selected
        (Exists Word64
          (λ borrowLow →
            borrowResults oldLow dl low borrowLow
            ∧
            Exists Word64
              (λ borrowHigh →
                subtractInt
                  (unsignedZ high)
                  (multiplyInt radixZ (unsignedZ borrowHigh))
                  ≡ subtractInt
                      (subtractInt
                        (unsignedZ oldHigh)
                        (unsignedZ dh))
                      (unsignedZ borrowLow)
                ∧ zeroZ ≤Z unsignedZ borrowHigh
                ∧ unsignedZ borrowHigh ≤Z oneZ
                ∧ qh ≡ one64)))
        ((high ≡ oldHigh ∧ low ≡ oldLow) ∧ qh ≡ zero64))

finalResult :
  {Zone : Set} →
  Word32 → Ptr Zone Word64 → Ptr Zone Word64 →
  Ptr Zone Word64 → Word64 → Ptr Zone Word64 → Set
finalResult sx x y qState qh resultState =
  value x (signed32 sx)
  ≡ addInt
      (multiplyInt
        (addInt
          (value qState (subtractInt (signed32 sx) twoZ))
          (multiplyInt
            (powerInt radixZ
              (subtractInt (signed32 sx) twoZ))
            (unsignedZ qh)))
        (value y twoZ))
      (value resultState twoZ)
  ∧ value resultState twoZ <Z value y twoZ
  ∧ zeroZ ≤Z unsignedZ qh
  ∧ unsignedZ qh ≤Z oneZ

mutual
  allLoopStates :
    {Zone : Set} →
    Word32 → Ptr Zone Word64 → Ptr Zone Word64 →
    Ptr Zone Word64 →
    Word64 → Word64 → Word64 → Word64 → Set
  allLoopStates sx x y initialQ qh dinv dh dl =
    (i : Word32) →
    (low high : Word64) →
    (xp qState : Ptr _ Word64) →
    sameShape qState initialQ →
    loopState sx x y qState qh low high xp (signed32 i) →
    loopStep sx x y qState qh i dinv dh dl low high xp

  loopStep :
    {Zone : Set} →
    Word32 → Ptr Zone Word64 → Ptr Zone Word64 →
    Ptr Zone Word64 → Word64 → Word32 →
    Word64 → Word64 → Word64 → Word64 → Word64 →
    Ptr Zone Word64 → Set
  loopStep sx x y qState qh i dinv dh dl low high xp =
    IfSet
      (intLess zeroZ (signed32 i))
      (positiveLoopStep
        sx x y qState qh i dinv dh dl low high xp)
      (finalLoopStep sx x y qState qh low high)

  positiveLoopStep :
    {Zone : Set} →
    Word32 → Ptr Zone Word64 → Ptr Zone Word64 →
    Ptr Zone Word64 → Word64 → Word32 →
    Word64 → Word64 → Word64 → Word64 → Word64 →
    Ptr Zone Word64 → Set
  positiveLoopStep sx x y qState qh i dinv dh dl low high xp =
    cursorAt xp (addInt (off xp) negativeOneZ)
    ∧
    ((work : Ptr _ Word64) →
      shiftedBy work xp negativeOneZ →
      accessAt work (off work)
      ∧
      ((halfRadixZ ≤Z unsignedZ dh
        ∧ reciprocal3by2 dinv dh dl
        ∧ remainderBound low high dl dh)
       ∧
       ((quotient resultLow resultHigh : Word64) →
        div3by2Premise
          work quotient resultLow resultHigh low high dl dh →
        int32InBounds (subtractInt (signed32 i) oneZ)
        ∧
        ((next : Word32) →
          signed32 next ≡ subtractInt (signed32 i) oneZ →
          accessAt qState
            (addInt (off qState) (signed32 next))
          ∧ writeable qState ≡ true
          ∧
          ((nextQ : Ptr _ Word64) →
            sameShape nextQ qState →
            updatedAt nextQ qState
              (addInt (off nextQ) (signed32 next))
              quotient →
            signed32 next <Z signed32 i
            ∧ loopState sx x y nextQ qh
                resultLow resultHigh work (signed32 next))))))

  div3by2Premise :
    {Zone : Set} →
    Ptr Zone Word64 → Word64 → Word64 → Word64 →
    Word64 → Word64 → Word64 → Word64 → Set
  div3by2Premise work quotient resultLow resultHigh
    currentLow currentHigh dl dh =
    addInt
      (addInt
        (addInt
          (multiplyInt (unsignedZ quotient) (unsignedZ dl))
          (multiplyInt
            (multiplyInt radixZ (unsignedZ quotient))
            (unsignedZ dh)))
        (unsignedZ resultLow))
      (multiplyInt radixZ (unsignedZ resultHigh))
    ≡ addInt
        (addInt
          (unsignedZ (pelts work (off work)))
          (multiplyInt radixZ (unsignedZ currentLow)))
        (multiplyInt
          (multiplyInt radixZ radixZ)
          (unsignedZ currentHigh))
    ∧ zeroZ ≤Z
        addInt
          (unsignedZ resultLow)
          (multiplyInt radixZ (unsignedZ resultHigh))
    ∧ remainderBound resultLow resultHigh dl dh

  finalLoopStep :
    {Zone : Set} →
    Word32 → Ptr Zone Word64 → Ptr Zone Word64 →
    Ptr Zone Word64 → Word64 → Word64 → Word64 → Set
  finalLoopStep sx x y qState qh low high =
    accessAt x (addInt (off x) oneZ)
    ∧ writeable x ≡ true
    ∧
    ((x1 : Ptr _ Word64) →
      sameShape x1 x →
      updatedAt x1 x (addInt (off x1) oneZ) high →
      accessAt x1 (off x1)
      ∧ writeable x1 ≡ true
      ∧
      ((x2 : Ptr _ Word64) →
        sameShape x2 x1 →
        FunctionEqual
          (pelts x2)
          (update (pelts x1) (off x2) low) →
        finalResult sx x y qState qh x2))

initialResults :
  {Zone : Set} →
  Word32 → Ptr Zone Word64 → Ptr Zone Word64 →
  Ptr Zone Word64 → Ptr Zone Word64 → Word32 →
  Word64 → Word64 → Word64 → Word64 → Word64 → Set
initialResults sx x y initialQ work index dinv dh dl oldHigh oldLow =
  (high low qh : Word64) →
  initialAdjustWitness high low qh dh dl oldHigh oldLow →
  loopState sx x y initialQ qh low high work (signed32 index)
  ∧ allLoopStates sx x y initialQ qh dinv dh dl

reciprocalObligation :
  {Zone : Set} →
  Word32 → Ptr Zone Word64 → Ptr Zone Word64 →
  Ptr Zone Word64 → Ptr Zone Word64 → Word32 →
  Word64 → Word64 → Word64 → Word64 → Set
reciprocalObligation sx x y initialQ work index dh dl oldHigh oldLow =
  (dinv : Word64) →
  reciprocal3by2 dinv dh dl →
  (adjustTest dh dl oldHigh oldLow ≡ true →
    (zeroZ ≤Z zeroZ ∧ zeroZ ≤Z oneZ)
    ∧ allBorrowResults oldLow dl)
  ∧ initialResults
      sx x y initialQ work index dinv dh dl oldHigh oldLow

indexObligation :
  {Zone : Set} →
  Word32 → Ptr Zone Word64 → Ptr Zone Word64 →
  Ptr Zone Word64 → Ptr Zone Word64 →
  Word64 → Word64 → Word64 → Word64 → Set
indexObligation sx x y initialQ work dh dl oldHigh oldLow =
  (index : Word32) →
  signed32 index ≡ subtractInt (signed32 sx) twoZ →
  halfRadixZ ≤Z unsignedZ dh
  ∧ reciprocalObligation
      sx x y initialQ work index dh dl oldHigh oldLow

loadedWork :
  {Zone : Set} →
  Word32 → Ptr Zone Word64 → Ptr Zone Word64 →
  Ptr Zone Word64 → Ptr Zone Word64 → Set
loadedWork sx x y initialQ work =
  accessAt y (addInt (off y) oneZ)
  ∧
  (let dh = pelts y (addInt (off y) oneZ)
   in
   accessAt y (off y)
   ∧
   (let dl = pelts y (off y)
    in
    accessAt work (addInt (off work) oneZ)
    ∧
    (let oldHigh = pelts work (addInt (off work) oneZ)
     in
     accessAt work (off work)
     ∧
     (let oldLow = pelts work (off work)
      in
      int32InBounds (subtractInt (signed32 sx) twoZ)
      ∧ indexObligation
          sx x y initialQ work dh dl oldHigh oldLow))))

displacementObligation :
  {Zone : Set} →
  Word32 → Ptr Zone Word64 → Ptr Zone Word64 →
  Ptr Zone Word64 → Set
displacementObligation sx x y initialQ =
  (displacement : Word32) →
  signed32 displacement ≡ subtractInt (signed32 sx) twoZ →
  cursorAt x (addInt (off x) (signed32 displacement))
  ∧
  ((work : Ptr _ Word64) →
    shiftedBy work x (signed32 displacement) →
    loadedWork sx x y initialQ work)

wmpn-divrem-2'vc : Set₁
wmpn-divrem-2'vc =
  (Zone : Set) →
  (sx : Word32) →
  (x y q : Ptr Zone Word64) →
  twoZ ≤Z signed32 sx →
  valid x (signed32 sx) →
  valid y twoZ →
  valid q (subtractInt (signed32 sx) twoZ) →
  halfRadixZ ≤Z
    unsignedZ (pelts y (addInt (off y) oneZ)) →
  writeable q ≡ true →
  writeable x ≡ true →
  int32InBounds (subtractInt (signed32 sx) twoZ)
  ∧ displacementObligation sx x y q
