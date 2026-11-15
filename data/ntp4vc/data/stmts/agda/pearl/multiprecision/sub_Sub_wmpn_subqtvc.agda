-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/sub_Sub_wmpn_subqtvc: the verification condition for
-- unequal-length multiprecision subtraction with shared-memory pointer
-- aliasing, borrow propagation, limb copying, and frame preservation.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module sub_Sub_wmpn_subqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; div-helper)

infix 4 _≤Z_ _<Z_
infixr 5 _∷V_ _∷L_
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

natDivide : Nat → Nat → Nat
natDivide n zero = zero
natDivide n (suc m) = div-helper zero m n m

natModulo : Nat → Nat → Nat
natModulo n zero = zero
natModulo n d@(suc _) =
  n - d * natDivide n d

euclideanModuloPositive : Int → Nat → Int
euclideanModuloPositive _ zero = pos zero
euclideanModuloPositive (pos n) d@(suc _) =
  pos (natModulo n d)
euclideanModuloPositive (negsuc n) d@(suc _) with natModulo (suc n) d
... | zero = pos zero
... | r@(suc _) = pos (d - r)

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

radixNat : Nat
radixNat = 18446744073709551616

int32InBounds : Int → Set
int32InBounds n = min32 ≤Z n ∧ n ≤Z max32

data Vec (A : Set) : Nat → Set where
  []V   : Vec A zero
  _∷V_  : {n : Nat} → A → Vec A n → Vec A (suc n)

replicateV : {A : Set} → (n : Nat) → A → Vec A n
replicateV zero value = []V
replicateV (suc n) value = value ∷V replicateV n value

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

zeroWord64 : Word64
zeroWord64 = replicateV 64 false

signed32 : Word32 → Int
signed32 bits with lastBit bits
... | false = pos (unsignedNat bits)
... | true =
  subtractInt (pos (unsignedNat bits)) (pos 4294967296)

data List (A : Set) : Set where
  []L   : List A
  _∷L_  : A → List A → List A

length : {A : Set} → List A → Nat
length []L = zero
length (value ∷L values) = suc (length values)

lookup : {A : Set} → A → Nat → List A → A
lookup default zero []L = default
lookup default zero (value ∷L values) = value
lookup default (suc index) []L = default
lookup default (suc index) (_ ∷L values) =
  lookup default index values

record Ptr (Zone A : Set) : Set where
  constructor pointer
  field
    contents  : List A
    off       : Int
    lo        : Int
    hi        : Int
    writeable : Bool
    region    : Zone

open Ptr public

pelts : {Zone : Set} → Ptr Zone Word64 → Int → Word64
pelts p index =
  lookup zeroWord64 (intToNat index) (contents p)

FunctionEq :
  {A B : Set} →
  (A → B) →
  (A → B) →
  Set
FunctionEq f g = (x : _) → f x ≡ g x

plength : {Zone : Set} → Ptr Zone Word64 → Int
plength p = pos (length (contents p))

valid : {Zone : Set} → Ptr Zone Word64 → Int → Set
valid p size =
  int32InBounds size
  ∧ zeroZ ≤Z size
  ∧ (zeroZ ≤Z lo p ∧ lo p ≤Z off p)
  ∧ addInt (off p) size ≤Z hi p
  ∧ hi p ≤Z plength p

aliasSafe :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Int →
  Int →
  Set
aliasSafe result operand resultSize operandSize =
  off result ≡ off operand
  ∨ addInt (off result) resultSize ≤Z off operand
  ∨ addInt (off operand) operandSize ≤Z off result

mapEqSub :
  {A : Set} →
  (Int → A) →
  (Int → A) →
  Int →
  Int →
  Set
mapEqSub current original lower upper =
  (index : Int) →
  (lower ≤Z index ∧ index <Z upper) →
  current index ≡ original index

update :
  {A : Set} →
  (Int → A) →
  Int →
  A →
  Int →
  A
update function index value query with intEqual query index
... | true = value
... | false = function query

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
  (index : Int) →
  (index <Z off current
   ∨ addInt (off current) size ≤Z index) →
  pelts current index ≡ pelts original index

accessAtIndex :
  {Zone : Set} →
  Ptr Zone Word64 →
  Int →
  Set
accessAtIndex p index =
  lo p ≤Z addInt (off p) index
  ∧ addInt (off p) index <Z hi p

borrowBounds : Word64 → Set
borrowBounds borrow =
  zeroZ ≤Z unsignedZ borrow
  ∧ unsignedZ borrow ≤Z oneZ

decrementModuloRadix : Word64 → Int
decrementModuloRadix limb =
  euclideanModuloPositive
    (subtractInt (unsignedZ limb) oneZ)
    radixNat

valueEquation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Int →
  Int →
  Int →
  Set
valueEquation currentR originalX originalY size sy borrow =
  subtractInt
      (value currentR size)
      (multiplyInt (powerInt radixZ size) borrow)
    ≡ subtractInt (value originalX size) (value originalY sy)

ySnapshot :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
ySnapshot newY newR oldY =
  contents newY ≡ contents newR
  ∧ length (contents newR) ≡ length (contents oldY)
  ∧ off newY ≡ off oldY
  ∧ lo newY ≡ lo oldY
  ∧ hi newY ≡ hi oldY
  ∧ writeable newY ≡ writeable oldY
  ∧ region newY ≡ region oldY

xSnapshot :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
xSnapshot newX newR oldX =
  contents newX ≡ contents newR
  ∧ length (contents newR) ≡ length (contents oldX)
  ∧ off newX ≡ off oldX
  ∧ lo newX ≡ lo oldX
  ∧ hi newX ≡ hi oldX
  ∧ writeable newX ≡ writeable oldX
  ∧ region newX ≡ region oldX

rSnapshot :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
rSnapshot newR oldR =
  length (contents newR) ≡ length (contents oldR)
  ∧ off newR ≡ off oldR
  ∧ lo newR ≡ lo oldR
  ∧ hi newR ≡ hi oldR
  ∧ writeable newR ≡ writeable oldR
  ∧ region newR ≡ region oldR

aliasState :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Int →
  Int →
  Set
aliasState stateR stateX stateY originalX originalY sx sy =
  FunctionEq (pelts stateX) (pelts stateR)
  ∧ FunctionEq (pelts stateY) (pelts stateR)
  ∧
    (off stateR ≡ off stateX
     ∨ mapEqSub
         (pelts stateX) (pelts originalX)
         (off stateX) (addInt (off stateX) sx))
  ∧
    (off stateR ≡ off stateY
     ∨ mapEqSub
         (pelts stateY) (pelts originalY)
         (off stateY) (addInt (off stateY) sy))

loopCore :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
loopCore originalR originalX originalY sx sy i borrow stateY stateX stateR =
  (signed32 sy ≤Z signed32 i ∧ signed32 i ≤Z signed32 sx)
  ∧ valueEquation
      stateR originalX originalY
      (signed32 i) (signed32 sy) (unsignedZ borrow)
  ∧ outsideUnchanged stateR originalR (signed32 i)
  ∧ aliasState
      stateR stateX stateY originalX originalY
      (signed32 sx) (signed32 sy)
  ∧ borrowBounds borrow

borrowInvariant :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
borrowInvariant
  originalR originalX originalY sx sy i borrow stateY stateX stateR =
  loopCore
    originalR originalX originalY sx sy i borrow stateY stateX stateR
  ∧ (i ≡ sx ∨ unsignedZ borrow ≡ oneZ)

copyInvariant :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
copyInvariant
  originalR originalX originalY sx sy i borrow stateY stateX stateR =
  (signed32 sy ≤Z signed32 i ∧ signed32 i ≤Z signed32 sx)
  ∧ (i ≡ sx ∨ unsignedZ borrow ≡ zeroZ)
  ∧ valueEquation
      stateR originalX originalY
      (signed32 i) (signed32 sy) (unsignedZ borrow)
  ∧ outsideUnchanged stateR originalR (signed32 i)
  ∧ aliasState
      stateR stateX stateY originalX originalY
      (signed32 sx) (signed32 sy)
  ∧ borrowBounds borrow

decreases :
  Word32 →
  Word32 →
  Word32 →
  Set
decreases sx current next =
  zeroZ ≤Z subtractInt (signed32 sx) (signed32 current)
  ∧ subtractInt (signed32 sx) (signed32 next)
      <Z subtractInt (signed32 sx) (signed32 current)

finished :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
finished originalR originalX originalY sx sy borrow stateY stateX stateR =
  valueEquation
      stateR originalX originalY
      (signed32 sx) (signed32 sy) (unsignedZ borrow)
  ∧ borrowBounds borrow
  ∧ outsideUnchanged stateR originalR (signed32 sx)
  ∧
    (off stateR ≡ off stateX
     ∨ mapEqSub
         (pelts stateX) (pelts originalX)
         (off stateX) (addInt (off stateX) (signed32 sx)))
  ∧
    (off stateR ≡ off stateY
     ∨ mapEqSub
         (pelts stateY) (pelts originalY)
         (off stateY) (addInt (off stateY) (signed32 sy)))

copyLoopStep :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word64 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
copyLoopStep
  originalR originalX originalY sx sy borrow i stateY stateX stateR =
  IfSet
    (intLess (signed32 i) (signed32 sx))
    (accessAtIndex stateX (signed32 i)
     ∧ accessAtIndex originalX (signed32 i)
     ∧ (accessAtIndex stateR (signed32 i)
        ∧ writeable stateR ≡ true)
     ∧
       ((newY newX newR : Ptr _ Word64) →
        ySnapshot newY newR stateY →
        xSnapshot newX newR stateX →
        rSnapshot newR stateR →
        (FunctionEq
           (pelts newR)
           (update
             (pelts stateR)
             (addInt (off newR) (signed32 i))
             (pelts stateX (addInt (off stateX) (signed32 i))))
         ∧ pelts newR (addInt (off newR) (signed32 i))
             ≡ pelts stateX (addInt (off stateX) (signed32 i))) →
        int32InBounds (addInt (signed32 i) oneZ)
        ∧
          ((nextI : Word32) →
           signed32 nextI ≡ addInt (signed32 i) oneZ →
           decreases sx i nextI
           ∧ copyInvariant
               originalR originalX originalY sx sy nextI borrow
               newY newX newR)))
    (finished
      originalR originalX originalY sx sy borrow stateY stateX stateR)

allCopyStates :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
allCopyStates
  originalR originalX originalY sx sy borrow baseY baseX baseR =
  (i : Word32) →
  (stateY stateX stateR : Ptr _ Word64) →
  ySnapshot stateY stateR baseY →
  xSnapshot stateX stateR baseX →
  rSnapshot stateR baseR →
  copyInvariant
    originalR originalX originalY sx sy i borrow stateY stateX stateR →
  copyLoopStep
    originalR originalX originalY sx sy borrow i stateY stateX stateR

afterBorrowWrite :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word64 →
  Word64 →
  Set
afterBorrowWrite
  originalR originalX originalY sx sy i oldY oldX oldR result borrow =
  (newY newX newR : Ptr _ Word64) →
  ySnapshot newY newR oldY →
  xSnapshot newX newR oldX →
  rSnapshot newR oldR →
  (FunctionEq
     (pelts newR)
     (update
       (pelts oldR)
       (addInt (off newR) (signed32 i))
       result)
   ∧ pelts newR (addInt (off newR) (signed32 i)) ≡ result) →
  int32InBounds (addInt (signed32 i) oneZ)
  ∧
    ((nextI : Word32) →
     signed32 nextI ≡ addInt (signed32 i) oneZ →
     (zeroFlag : Bool) →
     ((unsignedZ
          (pelts oldX (addInt (off oldX) (signed32 i))) ≡ zeroZ →
        zeroFlag ≡ true)
      ∧
       (zeroFlag ≡ true →
        pelts oldX (addInt (off oldX) (signed32 i)) ≡ zeroWord64)) →
     IfSet
       (notBool zeroFlag)
       (decreases sx i nextI
        ∧ copyInvariant
            originalR originalX originalY sx sy nextI zeroWord64
            newY newX newR
        ∧ allCopyStates
            originalR originalX originalY sx sy zeroWord64
            newY newX newR)
       (decreases sx i nextI
        ∧ borrowInvariant
            originalR originalX originalY sx sy nextI borrow
            newY newX newR))

borrowLoopStep :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
borrowLoopStep
  originalR originalX originalY sx sy i borrow stateY stateX stateR =
  IfSet
    (intLess (signed32 i) (signed32 sx))
    (accessAtIndex stateX (signed32 i)
     ∧ accessAtIndex originalX (signed32 i)
     ∧
       ((result : Word64) →
        unsignedZ result
          ≡ decrementModuloRadix
              (pelts stateX (addInt (off stateX) (signed32 i))) →
        (accessAtIndex stateR (signed32 i)
         ∧ writeable stateR ≡ true)
        ∧ afterBorrowWrite
            originalR originalX originalY sx sy i
            stateY stateX stateR result borrow))
    (copyInvariant
      originalR originalX originalY sx sy i borrow stateY stateX stateR
     ∧ allCopyStates
        originalR originalX originalY sx sy borrow stateY stateX stateR)

allBorrowStates :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
allBorrowStates
  originalR originalX originalY sx sy baseY baseX baseR =
  (i : Word32) →
  (borrow : Word64) →
  (stateY stateX stateR : Ptr _ Word64) →
  ySnapshot stateY stateR baseY →
  xSnapshot stateX stateR baseX →
  rSnapshot stateR baseR →
  borrowInvariant
    originalR originalX originalY sx sy i borrow stateY stateX stateR →
  borrowLoopStep
    originalR originalX originalY sx sy i borrow stateY stateX stateR

afterInitialSubtraction :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word64 →
  Set
afterInitialSubtraction r x y sx sy stateY stateX stateR borrow =
  (valueEquation
       stateR x y (signed32 sy) (signed32 sy) (unsignedZ borrow)
   ∧ borrowBounds borrow
   ∧ outsideUnchanged stateR r (signed32 sy)
   ∧
     (off stateR ≡ off stateX
      ∨ mapEqSub
          (pelts stateX) (pelts x)
          (off stateX) (addInt (off stateX) (signed32 sy)))
   ∧
     (off stateR ≡ off stateY
      ∨ mapEqSub
          (pelts stateY) (pelts y)
          (off stateY) (addInt (off stateY) (signed32 sy)))) →
    ((zeroFlag : Bool) →
     ((unsignedZ borrow ≡ zeroZ → zeroFlag ≡ true)
      ∧ (zeroFlag ≡ true → borrow ≡ zeroWord64)) →
     IfSet
       (notBool zeroFlag)
       (borrowInvariant
          r x y sx sy sy borrow stateY stateX stateR
        ∧ allBorrowStates r x y sx sy stateY stateX stateR)
       (copyInvariant
          r x y sx sy sy borrow stateY stateX stateR
        ∧ allCopyStates
            r x y sx sy borrow stateY stateX stateR))

initialSubtractionContinuation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Set
initialSubtractionContinuation r x y sx sy =
  (stateY stateX stateR : Ptr _ Word64) →
  ySnapshot stateY stateR y →
  xSnapshot stateX stateR x →
  rSnapshot stateR r →
  (borrow : Word64) →
  afterInitialSubtraction r x y sx sy stateY stateX stateR borrow

initialVC :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word32 →
  Set
initialVC r x y sx sy =
  zeroZ ≤Z signed32 sy
  ∧ valid r (signed32 sy)
  ∧ valid x (signed32 sy)
  ∧ valid y (signed32 sy)
  ∧ aliasSafe r x (signed32 sy) (signed32 sy)
  ∧ aliasSafe r y (signed32 sy) (signed32 sy)
  ∧ contents r ≡ contents x
  ∧ contents x ≡ contents y
  ∧ writeable r ≡ true
  ∧ initialSubtractionContinuation r x y sx sy

wmpn-sub'vc : Set₁
wmpn-sub'vc =
  (Zone : Set) →
  (sy sx : Word32) →
  (r x y : Ptr Zone Word64) →
  zeroZ ≤Z signed32 sy →
  signed32 sy ≤Z signed32 sx →
  valid r (signed32 sx) →
  valid x (signed32 sx) →
  valid y (signed32 sy) →
  aliasSafe r x (signed32 sx) (signed32 sx) →
  aliasSafe r y (signed32 sx) (signed32 sy) →
  contents r ≡ contents x →
  contents x ≡ contents y →
  writeable r ≡ true →
  initialVC r x y sx sy
