-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/sub_Sub_wmpn_sub_nqtvc: the loop verification condition
-- for equal-length multiprecision subtraction with pointer aliasing, borrow
-- arithmetic, memory updates, and frame preservation. This file contains no proof.

{-# OPTIONS --safe #-}

module sub_Sub_wmpn_sub_nqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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
length (_ ∷L values) = suc (length values)

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
  Set
aliasSafe result operand size =
  off result ≡ off operand
  ∨ addInt (off result) size ≤Z off operand
  ∨ addInt (off operand) size ≤Z off result

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

FunctionEqual :
  {A B : Set} →
  (A → B) →
  (A → B) →
  Set
FunctionEqual f g = (x : _) → f x ≡ g x

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

valueEquation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Int →
  Int →
  Set
valueEquation currentR originalX originalY size borrow =
  subtractInt
      (value currentR size)
      (multiplyInt
        (powerInt radixZ size)
        borrow)
    ≡ subtractInt
        (value originalX size)
        (value originalY size)

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
  Set
aliasState stateR stateX stateY originalX originalY size =
  FunctionEqual (pelts stateX) (pelts stateR)
  ∧ FunctionEqual (pelts stateR) (pelts stateY)
  ∧
    (off stateR ≡ off stateX
     ∨ mapEqSub
         (pelts stateX)
         (pelts originalX)
         (off stateX)
         (addInt (off stateX) size))
  ∧
    (off stateR ≡ off stateY
     ∨ mapEqSub
         (pelts stateY)
         (pelts originalY)
         (off stateY)
         (addInt (off stateY) size))

loopInvariant :
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
loopInvariant originalR originalX originalY size i borrow stateY stateX stateR =
  (zeroZ ≤Z signed32 i ∧ signed32 i ≤Z signed32 size)
  ∧ valueEquation
      stateR originalX originalY (signed32 i) (unsignedZ borrow)
  ∧ outsideUnchanged stateR originalR (signed32 i)
  ∧ aliasState
      stateR stateX stateY originalX originalY (signed32 size)
  ∧ borrowBounds borrow

decreases :
  Word32 →
  Word32 →
  Word32 →
  Set
decreases size current next =
  zeroZ ≤Z subtractInt (signed32 size) (signed32 current)
  ∧ subtractInt (signed32 size) (signed32 next)
      <Z subtractInt (signed32 size) (signed32 current)

nextInvariant :
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
nextInvariant
  originalR originalX originalY size i nextI borrow stateY stateX stateR =
  decreases size i nextI
  ∧ (zeroZ ≤Z signed32 nextI ∧ signed32 nextI ≤Z signed32 size)
  ∧ valueEquation
      stateR originalX originalY (signed32 nextI) (unsignedZ borrow)
  ∧ outsideUnchanged stateR originalR (signed32 nextI)
  ∧ aliasState
      stateR stateX stateY originalX originalY (signed32 size)
  ∧ borrowBounds borrow

afterWrite :
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
afterWrite
  originalR originalX originalY size i borrow newY newX newR =
  int32InBounds (addInt (signed32 i) oneZ)
  ∧
    ((nextI : Word32) →
      signed32 nextI ≡ addInt (signed32 i) oneZ →
      nextInvariant
        originalR originalX originalY size i nextI borrow newY newX newR)

updatedStates :
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
  Word64 →
  Set
updatedStates
  originalR originalX originalY size i oldY oldX oldR result borrow =
  (newY newX newR : Ptr _ Word64) →
  ySnapshot newY newR oldY →
  xSnapshot newX newR oldX →
  rSnapshot newR oldR →
  (FunctionEqual
     (pelts newR)
     (update
       (pelts oldR)
       (addInt (off newR) (signed32 i))
       result)
   ∧ pelts newR (addInt (off newR) (signed32 i)) ≡ result) →
  afterWrite
    originalR originalX originalY size i borrow newY newX newR

afterSubWithBorrow :
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
  Word64 →
  Set
afterSubWithBorrow
  originalR originalX originalY size i stateY stateX stateR result borrow =
  (accessAtIndex stateR (signed32 i)
   ∧ writeable stateR ≡ true)
  ∧ updatedStates
      originalR originalX originalY size i
      stateY stateX stateR result borrow

subWithBorrowEquation :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Word64 →
  Word64 →
  Set
subWithBorrowEquation stateX stateY i inputBorrow result borrow =
  subtractInt
      (unsignedZ result)
      (multiplyInt radixZ (unsignedZ borrow))
    ≡ subtractInt
        (subtractInt
          (unsignedZ
            (pelts stateX
              (addInt (off stateX) (signed32 i))))
          (unsignedZ
            (pelts stateY
              (addInt (off stateY) (signed32 i)))))
        (unsignedZ inputBorrow)

subWithBorrowStep :
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
subWithBorrowStep
  originalR originalX originalY size i inputBorrow stateY stateX stateR =
  (result borrow : Word64) →
  (subWithBorrowEquation stateX stateY i inputBorrow result borrow
   ∧ borrowBounds borrow) →
  afterSubWithBorrow
    originalR originalX originalY size i stateY stateX stateR result borrow

bodyStep :
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
bodyStep
  originalR originalX originalY size i inputBorrow stateY stateX stateR =
  accessAtIndex stateX (signed32 i)
  ∧ accessAtIndex stateY (signed32 i)
  ∧ accessAtIndex originalX (signed32 i)
  ∧ accessAtIndex originalY (signed32 i)
  ∧ borrowBounds inputBorrow
  ∧ subWithBorrowStep
      originalR originalX originalY size i inputBorrow stateY stateX stateR

finished :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Set
finished originalR originalX originalY size borrow stateY stateX stateR =
  valueEquation
      stateR originalX originalY (signed32 size) (unsignedZ borrow)
  ∧ borrowBounds borrow
  ∧ outsideUnchanged stateR originalR (signed32 size)
  ∧
    (off stateR ≡ off stateX
     ∨ mapEqSub
         (pelts stateX)
         (pelts originalX)
         (off stateX)
         (addInt (off stateX) (signed32 size)))
  ∧
    (off stateR ≡ off stateY
     ∨ mapEqSub
         (pelts stateY)
         (pelts originalY)
         (off stateY)
         (addInt (off stateY) (signed32 size)))

loopStep :
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
loopStep originalR originalX originalY size i borrow stateY stateX stateR =
  IfSet
    (intLess (signed32 i) (signed32 size))
    (bodyStep
      originalR originalX originalY size i borrow stateY stateX stateR)
    (finished
      originalR originalX originalY size borrow stateY stateX stateR)

allLoopStates :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Set
allLoopStates originalR originalX originalY size =
  (i : Word32) →
  (borrow : Word64) →
  (stateY stateX stateR : Ptr _ Word64) →
  ySnapshot stateY stateR originalY →
  xSnapshot stateX stateR originalX →
  rSnapshot stateR originalR →
  loopInvariant
    originalR originalX originalY size i borrow stateY stateX stateR →
  loopStep
    originalR originalX originalY size i borrow stateY stateX stateR

initialVC :
  {Zone : Set} →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Ptr Zone Word64 →
  Word32 →
  Set
initialVC r x y size =
  zeroZ ≤Z zeroZ
  ∧ zeroZ ≤Z signed32 size
  ∧ valueEquation r x y zeroZ zeroZ
  ∧ FunctionEqual (pelts x) (pelts r)
  ∧ FunctionEqual (pelts r) (pelts y)
  ∧
    (off r ≡ off x
     ∨ mapEqSub
         (pelts x)
         (pelts x)
         (off x)
         (addInt (off x) (signed32 size)))
  ∧
    (off r ≡ off y
     ∨ mapEqSub
         (pelts y)
         (pelts y)
         (off y)
         (addInt (off y) (signed32 size)))
  ∧ zeroZ ≤Z zeroZ
  ∧ zeroZ ≤Z oneZ
  ∧ allLoopStates r x y size

wmpn-sub-n'vc : Set₁
wmpn-sub-n'vc =
  (Zone : Set) →
  (size : Word32) →
  (r x y : Ptr Zone Word64) →
  zeroZ ≤Z signed32 size →
  valid r (signed32 size) →
  valid x (signed32 size) →
  valid y (signed32 size) →
  aliasSafe r x (signed32 size) →
  aliasSafe r y (signed32 size) →
  contents r ≡ contents x →
  contents x ≡ contents y →
  writeable r ≡ true →
  initialVC r x y size
