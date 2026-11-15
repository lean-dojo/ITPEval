-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/div_Div_wmpn_divrem_1qtvc: the verification condition
-- for one-limb multiprecision division, covering normalized and unnormalized
-- divisors, loop invariants, quotient writes, and remainder bounds. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module div_Div_wmpn_divrem_1qtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; div-helper)

infix 4 _≤Z_ _<Z_
infixr 5 _∷V_
infixr 3 _∧_
infixr 2 _∨_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

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

euclideanModuloPositive : Int → Nat → Int
euclideanModuloPositive _ zero = pos zero
euclideanModuloPositive (pos n) d@(suc _) = pos (natModulo n d)
euclideanModuloPositive (negsuc n) d@(suc _) with natModulo (suc n) d
... | zero = pos zero
... | r@(suc _) = pos (d - r)

moduloInt : Int → Int → Int
moduloInt dividend divisor =
  euclideanModuloPositive dividend (absoluteNat divisor)

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

zero64 : Word64
zero64 = natToVec 64 0

negativeOneZ zeroZ oneZ twoZ sixtyFourZ : Int
negativeOneZ = negsuc 0
zeroZ = pos 0
oneZ = pos 1
twoZ = pos 2
sixtyFourZ = pos 64

min32 max32 radixZ max64Z halfRadixZ : Int
min32 = negsuc 2147483647
max32 = pos 2147483647
radixZ = pos 18446744073709551616
max64Z = pos 18446744073709551615
halfRadixZ = pos 9223372036854775808

radixNat reciprocalNumeratorNat : Nat
radixNat = 18446744073709551616
reciprocalNumeratorNat = radixNat * radixNat - 1

int32InBounds : Int → Set
int32InBounds n = min32 ≤Z n ∧ n ≤Z max32

uint64InBounds : Int → Set
uint64InBounds n = zeroZ ≤Z n ∧ n ≤Z max64Z

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

sameFrame :
  {Zone : Set} → Ptr Zone Word64 → Ptr Zone Word64 → Set
sameFrame newer older =
  cellCount newer ≡ cellCount older
  ∧ off newer ≡ off older
  ∧ lo newer ≡ lo older
  ∧ hi newer ≡ hi older
  ∧ writeable newer ≡ writeable older
  ∧ region newer ≡ region older

FunctionEqual :
  {A B : Set} → (A → B) → (A → B) → Set
FunctionEqual f g = (x : _) → f x ≡ g x

update :
  {A : Set} → (Int → A) → Int → A → Int → A
update f index value query with intEqual query index
... | true = value
... | false = f query

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

reciprocal : Word64 → Word64 → Set
reciprocal v d =
  unsignedZ v ≡
  subtractInt
    (pos (natDivide reciprocalNumeratorNat (unsignedNat d)))
    radixZ

IndexBounds : Word32 → Word32 → Set
IndexBounds i msb =
  negativeOneZ ≤Z signed32 i
  ∧ signed32 i ≤Z signed32 msb

InitialNormalizedInvariant :
  {Zone : Set} →
  Int → Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word32 → Word64 → Set
InitialNormalizedInvariant mult x q sz msb ry =
  IndexBounds msb msb
  ∧ zeroZ <Z unsignedZ ry
  ∧ multiplyInt mult
      (valueSub (pelts x)
        (addInt (addInt (off x) (signed32 msb)) oneZ)
        (addInt (off x) (signed32 sz)))
    ≡ addInt
        (multiplyInt
          (valueSub (pelts q)
            (addInt (addInt (off q) (signed32 msb)) oneZ)
            (addInt (off q) (signed32 sz)))
          (unsignedZ ry))
        zeroZ
  ∧ zeroZ ≤Z subtractInt radixZ mult
  ∧ moduloInt zeroZ mult ≡ zeroZ

NormalizedLoopInvariant :
  {Zone : Set} →
  Int → Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word32 → Word64 → Word64 → Word32 → Set
NormalizedLoopInvariant mult x q sz msb ry r i =
  IndexBounds i msb
  ∧ unsignedZ r <Z unsignedZ ry
  ∧ multiplyInt mult
      (valueSub (pelts x)
        (addInt (addInt (off x) (signed32 i)) oneZ)
        (addInt (off x) (signed32 sz)))
    ≡ addInt
        (multiplyInt
          (valueSub (pelts q)
            (addInt (addInt (off q) (signed32 i)) oneZ)
            (addInt (off q) (signed32 sz)))
          (unsignedZ ry))
        (unsignedZ r)
  ∧ unsignedZ r ≤Z subtractInt radixZ mult
  ∧ moduloInt (unsignedZ r) mult ≡ zeroZ

InitialPlainInvariant :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word32 → Word64 → Set
InitialPlainInvariant x q sz msb y =
  IndexBounds msb msb
  ∧ zeroZ <Z unsignedZ y
  ∧ valueSub (pelts x)
      (addInt (addInt (off x) (signed32 msb)) oneZ)
      (addInt (off x) (signed32 sz))
    ≡ addInt
        (multiplyInt
          (valueSub (pelts q)
            (addInt (addInt (off q) (signed32 msb)) oneZ)
            (addInt (off q) (signed32 sz)))
          (unsignedZ y))
        zeroZ

PlainLoopInvariant :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word32 → Word64 → Word64 → Word32 → Set
PlainLoopInvariant x q sz msb y r i =
  IndexBounds i msb
  ∧ unsignedZ r <Z unsignedZ y
  ∧ valueSub (pelts x)
      (addInt (addInt (off x) (signed32 i)) oneZ)
      (addInt (off x) (signed32 sz))
    ≡ addInt
        (multiplyInt
          (valueSub (pelts q)
            (addInt (addInt (off q) (signed32 i)) oneZ)
            (addInt (off q) (signed32 sz)))
          (unsignedZ y))
        (unsignedZ r)

UpdatedPointer :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 → Word32 → Word64 → Set
UpdatedPointer newer older i quotient =
  FunctionEqual
    (pelts newer)
    (update
      (pelts older)
      (addInt (off newer) (signed32 i))
      quotient)
  ∧ pelts newer (addInt (off newer) (signed32 i)) ≡ quotient

NormalizedAfterStore :
  {Zone : Set} →
  Int → Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word32 → Word64 → Word64 → Word32 → Set
NormalizedAfterStore mult x q sz msb ry remainder i =
  int32InBounds (subtractInt (signed32 i) oneZ)
  ∧
  ((next : Word32) →
    signed32 next ≡ subtractInt (signed32 i) oneZ →
    signed32 next <Z signed32 i
    ∧ IndexBounds next msb
    ∧ unsignedZ remainder <Z unsignedZ ry
    ∧ multiplyInt mult
        (valueSub (pelts x)
          (addInt (addInt (off x) (signed32 next)) oneZ)
          (addInt (off x) (signed32 sz)))
      ≡ addInt
          (multiplyInt
            (valueSub (pelts q)
              (addInt (addInt (off q) (signed32 next)) oneZ)
              (addInt (off q) (signed32 sz)))
            (unsignedZ ry))
          (unsignedZ remainder)
    ∧ unsignedZ remainder ≤Z subtractInt radixZ mult
    ∧ moduloInt (unsignedZ remainder) mult ≡ zeroZ)

PlainAfterStore :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word32 → Word64 → Word64 → Word32 → Set
PlainAfterStore x q sz msb y remainder i =
  int32InBounds (subtractInt (signed32 i) oneZ)
  ∧
  ((next : Word32) →
    signed32 next ≡ subtractInt (signed32 i) oneZ →
    signed32 next <Z signed32 i
    ∧ IndexBounds next msb
    ∧ unsignedZ remainder <Z unsignedZ y
    ∧ valueSub (pelts x)
        (addInt (addInt (off x) (signed32 next)) oneZ)
        (addInt (off x) (signed32 sz))
      ≡ addInt
          (multiplyInt
            (valueSub (pelts q)
              (addInt (addInt (off q) (signed32 next)) oneZ)
              (addInt (off q) (signed32 sz)))
            (unsignedZ y))
          (unsignedZ remainder))

NormalizedStore :
  {Zone : Set} →
  Int → Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word32 → Word64 → Word64 → Word32 → Word64 → Set
NormalizedStore {Zone} mult x q1 sz msb ry remainder i quotient =
  (q2 : Ptr Zone Word64) →
  sameFrame q2 q1 →
  UpdatedPointer q2 q1 i quotient →
  NormalizedAfterStore mult x q2 sz msb ry remainder i

PlainStore :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word32 → Word64 → Word64 → Word32 → Word64 → Set
PlainStore {Zone} x q1 sz msb y remainder i quotient =
  (q2 : Ptr Zone Word64) →
  sameFrame q2 q1 →
  UpdatedPointer q2 q1 i quotient →
  PlainAfterStore x q2 sz msb y remainder i

NormalizedValueUpdate :
  {Zone : Set} →
  Int → Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word32 → Word64 → Word64 → Word32 → Word64 → Set
NormalizedValueUpdate mult x q1 sz msb ry remainder i quotient =
  let upper = addInt (off q1) (signed32 sz)
      middle = addInt (addInt (off q1) oneZ) (signed32 i)
      index = addInt (off q1) (signed32 i)
      old = pelts q1
  in
  (middle ≤Z upper ∧ (index <Z middle ∨ upper ≤Z index))
  ∧
  (valueSub old middle upper
    ≡ valueSub (update old index quotient) middle upper →
   accessAt q1 (addInt (off q1) (signed32 i))
   ∧ writeable q1 ≡ true
   ∧ NormalizedStore mult x q1 sz msb ry remainder i quotient)

PlainValueUpdate :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word32 → Word64 → Word64 → Word32 → Word64 → Set
PlainValueUpdate x q1 sz msb y remainder i quotient =
  let upper = addInt (off q1) (signed32 sz)
      middle = addInt (addInt (off q1) oneZ) (signed32 i)
      index = addInt (off q1) (signed32 i)
      old = pelts q1
  in
  (middle ≤Z upper ∧ (index <Z middle ∨ upper ≤Z index))
  ∧
  (valueSub old middle upper
    ≡ valueSub (update old index quotient) middle upper →
   accessAt q1 (addInt (off q1) (signed32 i))
   ∧ writeable q1 ≡ true
   ∧ PlainStore x q1 sz msb y remainder i quotient)

NormalizedDivisionStep :
  {Zone : Set} →
  Int → Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word32 → Word64 → Word64 → Word32 →
  Word64 → Word64 → Set
NormalizedDivisionStep mult x q1 sz msb ry v i low combined =
  (quotient remainder : Word64) →
  addInt
    (multiplyInt (unsignedZ quotient) (unsignedZ ry))
    (unsignedZ remainder)
    ≡
  addInt
    (unsignedZ low)
    (multiplyInt radixZ (unsignedZ combined))
  →
  zeroZ ≤Z unsignedZ remainder →
  unsignedZ remainder <Z unsignedZ ry →
  Not (mult ≡ zeroZ)
  ∧ NormalizedValueUpdate
      mult x q1 sz msb ry remainder i quotient

PlainDivisionStep :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word32 → Word64 → Word64 → Word32 → Set
PlainDivisionStep x q1 sz msb y r i =
  (quotient remainder : Word64) →
  addInt
    (multiplyInt (unsignedZ quotient) (unsignedZ y))
    (unsignedZ remainder)
    ≡
  addInt
    (unsignedZ (pelts x (addInt (off x) (signed32 i))))
    (multiplyInt radixZ (unsignedZ r))
  →
  zeroZ ≤Z unsignedZ remainder →
  unsignedZ remainder <Z unsignedZ y →
  PlainValueUpdate x q1 sz msb y remainder i quotient

NormalizedCombined :
  {Zone : Set} →
  Int → Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word32 → Word32 → Word64 → Word64 →
  Word64 → Word64 → Word64 → Set
NormalizedCombined mult x q1 sz msb i ry v r low high =
  (combined : Word64) →
  unsignedZ combined ≡ addInt (unsignedZ r) (unsignedZ high) →
  (halfRadixZ ≤Z unsignedZ ry
   ∧ unsignedZ combined <Z unsignedZ ry
   ∧ reciprocal v ry)
  ∧ NormalizedDivisionStep
      mult x q1 sz msb ry v i low combined

NormalizedShiftedLimb :
  {Zone : Set} →
  Int → Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word32 → Word32 → Word64 → Word64 →
  Word64 → Word64 → Set
NormalizedShiftedLimb mult x q1 sz msb i ry v r shift =
  (low high : Word64) →
  addInt
    (unsignedZ low)
    (multiplyInt radixZ (unsignedZ high))
    ≡
  multiplyInt
    (powerInt twoZ (unsignedZ shift))
    (unsignedZ (pelts x (addInt (off x) (signed32 i))))
  →
  moduloInt
    (unsignedZ low)
    (powerInt twoZ (unsignedZ shift))
    ≡ zeroZ
  →
  unsignedZ low ≤Z
    subtractInt radixZ (powerInt twoZ (unsignedZ shift))
  →
  unsignedZ high <Z powerInt twoZ (unsignedZ shift)
  →
  uint64InBounds (addInt (unsignedZ r) (unsignedZ high))
  ∧ NormalizedCombined
      mult x q1 sz msb i ry v r low high

NormalizedIteration :
  {Zone : Set} →
  Int → Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word32 → Word32 → Word32 →
  Word64 → Word64 → Word64 → Set
NormalizedIteration mult x q1 sz msb clz i ry v r =
  accessAt x (addInt (off x) (signed32 i))
  ∧ zeroZ ≤Z signed32 clz
  ∧
  ((shift : Word64) →
    unsignedZ shift ≡ signed32 clz →
    (zeroZ <Z unsignedZ shift ∧ unsignedZ shift <Z sixtyFourZ)
    ∧ NormalizedShiftedLimb
        mult x q1 sz msb i ry v r shift)

NormalizedFinish :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word32 → Word32 → Word64 → Word64 → Set
NormalizedFinish x q1 sz clz i y r =
  zeroZ ≤Z signed32 clz
  ∧
  ((shift : Word64) →
    unsignedZ shift ≡ signed32 clz →
    ((zeroZ ≤Z unsignedZ shift ∧ unsignedZ shift <Z sixtyFourZ)
     ∧ moduloInt
         (unsignedZ r)
         (powerInt twoZ (unsignedZ shift))
         ≡ zeroZ)
    ∧
    ((res : Word64) →
      unsignedZ r ≡
        multiplyInt
          (powerInt twoZ (unsignedZ shift))
          (unsignedZ res)
      →
      zeroZ ≤Z signed32 clz
      ∧
      ((shift-again : Word64) →
        unsignedZ shift-again ≡ signed32 clz →
        ((zeroZ ≤Z unsignedZ shift-again
          ∧ unsignedZ shift-again <Z sixtyFourZ)
         ∧ moduloInt
             (unsignedZ r)
             (powerInt twoZ (unsignedZ shift-again))
             ≡ zeroZ)
        ∧
        ((result : Word64) →
          unsignedZ r ≡
            multiplyInt
              (powerInt twoZ (unsignedZ shift-again))
              (unsignedZ result)
          →
          value x (signed32 sz)
            ≡ addInt
                (multiplyInt
                  (value q1 (signed32 sz))
                  (unsignedZ y))
                (unsignedZ result)
          ∧ unsignedZ result <Z unsignedZ y))))

NormalizedLoopBody :
  {Zone : Set} →
  Int → Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word32 → Word32 → Word64 → Word64 →
  Word64 → Word64 → Word32 → Set
NormalizedLoopBody mult x q1 sz msb clz y ry v r i =
  IfSet
    (intLessOrEqual zeroZ (signed32 i))
    (NormalizedIteration mult x q1 sz msb clz i ry v r)
    (NormalizedFinish x q1 sz clz i y r)

NormalizedAllLoops :
  {Zone : Set} →
  Int → Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word32 → Word32 → Word64 → Word64 →
  Word64 → Set
NormalizedAllLoops {Zone} mult x q sz msb clz y ry v =
  (r : Word64) →
  (i : Word32) →
  (q1 : Ptr Zone Word64) →
  sameFrame q1 q →
  NormalizedLoopInvariant mult x q1 sz msb ry r i →
  NormalizedLoopBody mult x q1 sz msb clz y ry v r i

NormalizedReciprocal :
  {Zone : Set} →
  Int → Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word32 → Word32 → Word64 → Word64 → Set
NormalizedReciprocal mult x q sz msb clz y ry =
  (v : Word64) →
  reciprocal v ry →
  InitialNormalizedInvariant mult x q sz msb ry
  ∧ NormalizedAllLoops mult x q sz msb clz y ry v

NormalizedDivisor :
  {Zone : Set} →
  Int → Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word32 → Word32 → Word64 → Word64 → Set
NormalizedDivisor mult x q sz msb clz y shift =
  (ry : Word64) →
  unsignedZ ry ≡
    multiplyInt
      (powerInt twoZ (unsignedZ shift))
      (unsignedZ y)
  →
  halfRadixZ ≤Z unsignedZ ry
  ∧ NormalizedReciprocal mult x q sz msb clz y ry

NormalizedBranch :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word32 → Word32 → Word64 → Set
NormalizedBranch x q sz msb clz y =
  let mult = powerInt twoZ (signed32 clz)
  in
  zeroZ ≤Z signed32 clz
  ∧
  ((shift : Word64) →
    unsignedZ shift ≡ signed32 clz →
    ((zeroZ ≤Z unsignedZ shift
      ∧ unsignedZ shift <Z sixtyFourZ)
     ∧ multiplyInt
         (powerInt twoZ (unsignedZ shift))
         (unsignedZ y)
       ≤Z max64Z)
    ∧ NormalizedDivisor mult x q sz msb clz y shift)

PlainIteration :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word32 → Word64 → Word64 → Word64 → Word32 → Set
PlainIteration x q1 sz msb y v r i =
  accessAt x (addInt (off x) (signed32 i))
  ∧
  ((halfRadixZ ≤Z unsignedZ y
    ∧ unsignedZ r <Z unsignedZ y
    ∧ reciprocal v y)
   ∧ PlainDivisionStep x q1 sz msb y r i)

PlainFinish :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word64 → Word64 → Set
PlainFinish x q1 sz y r =
  value x (signed32 sz)
    ≡ addInt
        (multiplyInt (value q1 (signed32 sz)) (unsignedZ y))
        (unsignedZ r)
  ∧ unsignedZ r <Z unsignedZ y

PlainLoopBody :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word32 → Word64 → Word64 → Word64 → Word32 → Set
PlainLoopBody x q1 sz msb y v r i =
  IfSet
    (intLessOrEqual zeroZ (signed32 i))
    (PlainIteration x q1 sz msb y v r i)
    (PlainFinish x q1 sz y r)

PlainAllLoops :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word32 → Word64 → Word64 → Set
PlainAllLoops {Zone} x q sz msb y v =
  (r : Word64) →
  (i : Word32) →
  (q1 : Ptr Zone Word64) →
  sameFrame q1 q →
  PlainLoopInvariant x q1 sz msb y r i →
  PlainLoopBody x q1 sz msb y v r i

PlainBranch :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word32 → Word64 → Set
PlainBranch x q sz msb y =
  halfRadixZ ≤Z unsignedZ y
  ∧
  ((v : Word64) →
    reciprocal v y →
    InitialPlainInvariant x q sz msb y
    ∧ PlainAllLoops x q sz msb y v)

CountLeadingZerosObligation :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word32 → Word64 → Word32 → Set
CountLeadingZerosObligation x q sz msb y clz =
  multiplyInt (powerInt twoZ (signed32 clz)) (unsignedZ y)
      ≤Z max64Z
  ∧ max64Z <Z
      multiplyInt twoZ
        (multiplyInt
          (powerInt twoZ (signed32 clz))
          (unsignedZ y))
  ∧ zeroZ ≤Z signed32 clz
  ∧ signed32 clz <Z sixtyFourZ
  →
  IfSet
    (intLess zeroZ (signed32 clz))
    (NormalizedBranch x q sz msb clz y)
    (PlainBranch x q sz msb y)

AfterMostSignificantIndex :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 →
  Word32 → Word64 → Word32 → Set
AfterMostSignificantIndex x q sz y msb =
  zeroZ <Z unsignedZ y
  ∧
  ((clz : Word32) →
    CountLeadingZerosObligation x q sz msb y clz)

wmpn-divrem-1'vc : Set₁
wmpn-divrem-1'vc =
  (Zone : Set) →
  (x : Ptr Zone Word64) →
  (sz : Word32) →
  (q : Ptr Zone Word64) →
  (y : Word64) →
  valid x (signed32 sz) →
  valid q (signed32 sz) →
  writeable q ≡ true →
  zeroZ <Z signed32 sz →
  zeroZ <Z unsignedZ y →
  int32InBounds (subtractInt (signed32 sz) oneZ)
  ∧
  ((msb : Word32) →
    signed32 msb ≡ subtractInt (signed32 sz) oneZ →
    AfterMostSignificantIndex x q sz y msb)
