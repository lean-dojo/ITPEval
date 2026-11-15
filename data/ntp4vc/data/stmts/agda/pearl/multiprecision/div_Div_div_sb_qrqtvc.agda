-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/div_Div_div_sb_qrqtvc: the verification condition for
-- normalized multiprecision quotient-and-remainder division, including
-- reciprocal quotient estimation, loop preservation, correction, and the
-- final quotient/remainder relation. This file contains no proof.

{-# OPTIONS --safe #-}

module div_Div_div_sb_qrqtvc where

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

natModulo : Nat → Nat → Nat
natModulo n zero = zero
natModulo n d@(suc _) = n - d * natDivide n d

euclideanModuloPositive : Int → Nat → Int
euclideanModuloPositive _ zero = pos zero
euclideanModuloPositive (pos n) d@(suc _) = pos (natModulo n d)
euclideanModuloPositive (negsuc n) d@(suc _) with natModulo (suc n) d
... | zero = pos zero
... | r@(suc _) = pos (d - r)

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

zero32 one32 : Word32
zero32 = natToVec 32 0
one32 = natToVec 32 1

zero64 one64 max64 : Word64
zero64 = natToVec 64 0
one64 = natToVec 64 1
max64 = natToVec 64 18446744073709551615

zeroZ oneZ twoZ threeZ : Int
zeroZ = pos 0
oneZ = pos 1
twoZ = pos 2
threeZ = pos 3

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

uint64InBounds : Int → Set
uint64InBounds n =
  zeroZ ≤Z n ∧ n ≤Z unsignedZ max64

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ _) = x
nthDefault default (suc _) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

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

validAtRange :
  {Zone : Set} → Ptr Zone Word64 → Int → Int → Set
validAtRange p start size =
  int32InBounds size
  ∧ zeroZ ≤Z size
  ∧ (zeroZ ≤Z lo p ∧ lo p ≤Z start)
  ∧ addInt start size ≤Z hi p
  ∧ hi p ≤Z plength p

accessAt : {Zone : Set} → Ptr Zone Word64 → Int → Set
accessAt p index = lo p ≤Z index ∧ index <Z hi p

cursorAt : {Zone : Set} → Ptr Zone Word64 → Int → Set
cursorAt p index = lo p ≤Z index ∧ index ≤Z hi p

sameFrame :
  {Zone : Set} → Ptr Zone Word64 → Ptr Zone Word64 → Set
sameFrame newer older =
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
  ∧ pelts shifted ≡ pelts base
  ∧ cellCount shifted ≡ cellCount base
  ∧ lo shifted ≡ lo base
  ∧ hi shifted ≡ hi base
  ∧ region shifted ≡ region base
  ∧ writeable shifted ≡ writeable base

sameStateShape :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 → Set
sameStateShape newer older =
  cellCount newer ≡ cellCount older
  ∧ off newer ≡ off older
  ∧ lo newer ≡ lo older
  ∧ hi newer ≡ hi older
  ∧ writeable newer ≡ writeable older
  ∧ region newer ≡ region older

aliasThrough :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 → Ptr Zone Word64 → Set
aliasThrough view backing oldView =
  memory view ≡ memory backing
  ∧ cellCount view ≡ cellCount backing
  ∧ cellCount backing ≡ cellCount oldView
  ∧ off view ≡ off oldView
  ∧ lo view ≡ lo oldView
  ∧ hi view ≡ hi oldView
  ∧ writeable view ≡ writeable oldView
  ∧ region view ≡ region oldView

copyOf : List Word64 → (Int → Word64) → Nat → Set
copyOf copied source sourceLength =
  length copied ≡ sourceLength
  ∧
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z pos (length copied)) →
    nthDefault zero64 (intToNat i) copied
      ≡ source i)

mapsEqual :
  {Zone : Set} → Ptr Zone Word64 → Ptr Zone Word64 → Set
mapsEqual first second =
  (index : Int) → pelts first index ≡ pelts second index

outsideUnchanged :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 → Int → Int → Set
outsideUnchanged newer older start size =
  (j : Int) →
  (j <Z start ∨ addInt start size ≤Z j) →
  pelts newer j ≡ pelts older j

update :
  {A : Set} → (Int → A) → Int → A → Int → A
update f index value query with intEqual query index
... | true = value
... | false = f query

storedAt :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 → Int → Word64 → Set
storedAt newer older index limb =
  sameFrame newer older
  ∧ ((query : Int) →
      pelts newer query ≡ update (pelts older) index limb query)
  ∧ pelts newer index ≡ limb

valueMapFrom : (Int → Word64) → Int → Nat → Int
valueMapFrom m index zero = zeroZ
valueMapFrom m index (suc count) =
  addInt
    (unsignedZ (m index))
    (multiplyInt
      radixZ
      (valueMapFrom m (addInt index oneZ) count))

valueAt :
  {Zone : Set} → Ptr Zone Word64 → Int → Int → Int
valueAt p index size =
  valueMapFrom (pelts p) index (intToNat size)

value : {Zone : Set} → Ptr Zone Word64 → Int → Int
value p size = valueAt p (off p) size

valueSub : (Int → Word64) → Int → Int → Int
valueSub m lower upper =
  valueMapFrom m lower (intToNat (subtractInt upper lower))

normalized :
  {Zone : Set} → Ptr Zone Word64 → Word32 → Set
normalized p size =
  valid p (signed32 size)
  ∧ halfRadixZ ≤Z
      unsignedZ
        (pelts p
          (subtractInt
            (addInt (off p) (signed32 size))
            oneZ))

reciprocal3by2 : Word64 → Word64 → Word64 → Set
reciprocal3by2 v dh dl =
  unsignedZ v ≡
  subtractInt
    (pos
      (natDivide reciprocal3NumeratorNat
        (unsignedNat dl + radixNat * unsignedNat dh)))
    radixZ

wordFlag64 : Word64 → Word64 → Bool → Set
wordFlag64 word constant flag =
  (unsignedZ word ≡ unsignedZ constant → flag ≡ true)
  ∧ (flag ≡ true → word ≡ constant)

andWordFlag64 :
  Word64 → Word64 → Word64 → Word64 → Bool → Set
andWordFlag64 first firstConstant second secondConstant result =
  Exists Bool
    (λ firstFlag →
      wordFlag64 first firstConstant firstFlag
      ∧ IfSet
          firstFlag
          (wordFlag64 second secondConstant result)
          (result ≡ false))

compareInt : Int → Int → Int
compareInt a b with intLess a b
... | true = negsuc 0
... | false with intLess b a
...   | true = pos 1
...   | false = pos 0

carryBounds : Word64 → Set
carryBounds carry =
  zeroZ ≤Z unsignedZ carry
  ∧ unsignedZ carry ≤Z oneZ

submulEffect :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 → Int →
  Ptr Zone Word64 → Int → Word64 → Word64 → Set
submulEffect newer older start divisor size factor borrow =
  subtractInt
    (valueAt newer start size)
    (multiplyInt (powerInt radixZ size) (unsignedZ borrow))
  ≡ subtractInt
      (valueAt older start size)
      (multiplyInt (value divisor size) (unsignedZ factor))
  ∧ outsideUnchanged newer older start size

initialSubmulEffect :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 → Int →
  Ptr Zone Word64 → Int → Word64 → Word64 → Set
initialSubmulEffect newer older start divisor size factor borrow =
  subtractInt
    (valueAt newer start size)
    (multiplyInt (powerInt radixZ size) (unsignedZ borrow))
  ≡ subtractInt
      (valueAt older start size)
      (multiplyInt (value divisor size) (unsignedZ factor))
  ∧ carryBounds borrow
  ∧ outsideUnchanged newer older start size

addEffect :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 → Int →
  Ptr Zone Word64 → Int → Word64 → Set
addEffect newer older start addend size carry =
  carryBounds carry
  ∧ addInt
      (valueAt newer start size)
      (multiplyInt (powerInt radixZ size) (unsignedZ carry))
    ≡ addInt
        (valueAt older start size)
        (value addend size)
  ∧ outsideUnchanged newer older start size

submulAt :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 → Int →
  Ptr Zone Word64 → Int → Word64 → Word64 → Set
submulAt newer older start divisor size factor borrow =
  sameFrame newer older
  ∧ subtractInt
      (valueAt newer start size)
      (multiplyInt (powerInt radixZ size) (unsignedZ borrow))
    ≡ subtractInt
        (valueAt older start size)
        (multiplyInt (value divisor size) (unsignedZ factor))
  ∧ outsideUnchanged newer older start size

addAt :
  {Zone : Set} →
  Ptr Zone Word64 → Ptr Zone Word64 → Int →
  Ptr Zone Word64 → Int → Word64 → Set
addAt newer older start addend size carry =
  sameFrame newer older
  ∧ addInt
      (valueAt newer start size)
      (multiplyInt (powerInt radixZ size) (unsignedZ carry))
    ≡ addInt
        (valueAt older start size)
        (value addend size)
  ∧ carryBounds carry
  ∧ outsideUnchanged newer older start size

div3by2Result :
  Word64 → Word64 → Word64 →
  Word64 → Word64 → Word64 →
  Word64 → Word64 → Word64 → Set
div3by2Result qu rl rh xh xm xl dh dl v =
  reciprocal3by2 v dh dl
  ∧ addInt
      (addInt
        (multiplyInt (unsignedZ qu) (unsignedZ dl))
        (multiplyInt
          (multiplyInt radixZ (unsignedZ qu))
          (unsignedZ dh)))
      (addInt (unsignedZ rl)
        (multiplyInt radixZ (unsignedZ rh)))
    ≡ addInt
        (unsignedZ xl)
        (addInt
          (multiplyInt radixZ (unsignedZ xm))
          (multiplyInt
            (multiplyInt radixZ radixZ)
            (unsignedZ xh)))
  ∧ zeroZ ≤Z
      addInt (unsignedZ rl)
        (multiplyInt radixZ (unsignedZ rh))
  ∧ addInt (unsignedZ rl)
      (multiplyInt radixZ (unsignedZ rh))
    <Z addInt (unsignedZ dl)
        (multiplyInt radixZ (unsignedZ dh))

loopInvariant :
  {Zone : Set} →
  Word32 → Word32 → Word32 → Word32 →
  Ptr Zone Word64 → Ptr Zone Word64 →
  Ptr Zone Word64 → Ptr Zone Word64 →
  Ptr Zone Word64 → Ptr Zone Word64 →
  Word64 → Word64 → Word64 → Word64 → Int → Set
loopInvariant sx sy i mdn originalX originalQ xState qState xp qp
  qh x1 dh dl vy =
  (zeroZ ≤Z signed32 i
   ∧ signed32 i ≤Z subtractInt (signed32 sx) (signed32 sy))
  ∧ off qp ≡ addInt (off qState) (signed32 i)
  ∧ off xp ≡
      subtractInt
        (addInt
          (addInt (off xState) (signed32 sy))
          (signed32 i))
        twoZ
  ∧ plength qp ≡ plength qState
  ∧ lo qp ≡ lo qState
  ∧ hi qp ≡ hi qState
  ∧ plength xp ≡ plength xState
  ∧ lo xp ≡ lo xState
  ∧ hi xp ≡ hi xState
  ∧ pelts qp ≡ pelts qState
  ∧ pelts xp ≡ pelts xState
  ∧ (writeable qp ≡ true ∧ writeable xp ≡ true)
  ∧ value originalX (signed32 sx)
    ≡ addInt
        (multiplyInt
          (multiplyInt
            (addInt
              (value qp
                (subtractInt
                  (subtractInt (signed32 sx) (signed32 sy))
                  (signed32 i)))
              (multiplyInt
                (unsignedZ qh)
                (powerInt radixZ
                  (subtractInt
                    (subtractInt (signed32 sx) (signed32 sy))
                    (signed32 i)))))
            vy)
          (powerInt radixZ (signed32 i)))
        (addInt
          (value xState
            (subtractInt
              (addInt (signed32 sy) (signed32 i))
              oneZ))
          (multiplyInt
            (powerInt radixZ
              (subtractInt
                (addInt (signed32 sy) (signed32 i))
                oneZ))
            (unsignedZ x1)))
  ∧ addInt
      (valueSub
        (pelts xState)
        (addInt
          (off xp)
          (signed32 mdn))
        (addInt
          (addInt (off xp) (signed32 mdn))
          (subtractInt (signed32 sy) oneZ)))
      (multiplyInt
        (powerInt radixZ
          (subtractInt (signed32 sy) oneZ))
        (unsignedZ x1))
    <Z vy
  ∧ addInt
      (unsignedZ
        (pelts xState (off xp)))
      (multiplyInt radixZ (unsignedZ x1))
    ≤Z addInt
        (unsignedZ dl)
        (multiplyInt radixZ (unsignedZ dh))

finalPost :
  {Zone : Set} →
  Word32 → Word32 →
  Ptr Zone Word64 → Ptr Zone Word64 →
  Ptr Zone Word64 → Ptr Zone Word64 →
  Word64 → Set
finalPost sx sy originalX divisor quotient remainder qh =
  value originalX (signed32 sx)
    ≡ addInt
        (multiplyInt
          (addInt
            (value quotient
              (subtractInt (signed32 sx) (signed32 sy)))
            (multiplyInt
              (powerInt radixZ
                (subtractInt (signed32 sx) (signed32 sy)))
              (unsignedZ qh)))
          (value divisor (signed32 sy)))
        (value remainder (signed32 sy))
  ∧ value remainder (signed32 sy)
      <Z value divisor (signed32 sy)
  ∧ carryBounds qh

mutual
  AllLoopStates :
    {Zone : Set} →
    Word32 → Word32 → Word32 →
    Ptr Zone Word64 → Ptr Zone Word64 →
    Ptr Zone Word64 → Ptr Zone Word64 →
    Word64 → Word64 → Word64 → Word64 → Int → Set
  AllLoopStates sx sy mdn originalX baseX originalQ divisor
    qh dh dl v vy =
    (x1 : Word64) →
    (i : Word32) →
    (qp xp xState qState : Ptr _ Word64) →
    sameStateShape xState baseX →
    sameStateShape qState originalQ →
    loopInvariant sx sy i mdn originalX originalQ
      xState qState xp qp qh x1 dh dl vy →
    IfSet
      (intLess zeroZ (signed32 i))
      (LoopBody sx sy i mdn originalX baseX originalQ divisor
        xState qState xp qp qh x1 dh dl v vy)
      (LoopExit sx sy i originalX divisor xState qState xp qh x1)

  LoopExit :
    {Zone : Set} →
    Word32 → Word32 → Word32 →
    Ptr Zone Word64 → Ptr Zone Word64 →
    Ptr Zone Word64 → Ptr Zone Word64 → Ptr Zone Word64 →
    Word64 → Word64 → Set
  LoopExit sx sy i originalX divisor xState qState xp qh x1 =
    let lower = off xState
        upper = off xp
        index = addInt (off xp) oneZ
        old = pelts xState
    in
    (lower ≤Z upper ∧ (index <Z lower ∨ upper ≤Z index))
    ∧
    (valueSub old lower upper
       ≡ valueSub (update old index x1) lower upper →
     (accessAt xp index ∧ writeable xp ≡ true)
     ∧
     ((storedView storedState : Ptr _ Word64) →
       aliasThrough storedView storedState xp →
       sameStateShape storedState xState →
       pelts storedView ≡ update (pelts xp) index x1
       ∧ pelts storedView index ≡ x1 →
       finalPost sx sy originalX divisor qState storedState qh))

  LoopBody :
    {Zone : Set} →
    Word32 → Word32 → Word32 → Word32 →
    Ptr Zone Word64 → Ptr Zone Word64 →
    Ptr Zone Word64 → Ptr Zone Word64 →
    Ptr Zone Word64 → Ptr Zone Word64 →
    Ptr Zone Word64 → Ptr Zone Word64 →
    Word64 → Word64 → Word64 → Word64 → Word64 → Int → Set
  LoopBody sx sy i mdn originalX baseX originalQ divisor
    xState qState xp qp qh x1 dh dl v vy =
    int32InBounds (subtractInt (signed32 i) oneZ)
    ∧
    ((nextI : Word32) →
      signed32 nextI ≡ subtractInt (signed32 i) oneZ →
      cursorAt xp (addInt (off xp) (negative 1))
      ∧
      ((xpShift : Ptr _ Word64) →
        shiftedBy xpShift xp (negative 1) →
        cursorAt xpShift
          (addInt (off xpShift) (signed32 mdn))
        ∧
        ((xd : Ptr _ Word64) →
          shiftedBy xd xpShift (signed32 mdn) →
          accessAt xpShift (addInt (off xpShift) oneZ)
          ∧
          (let nx0 = pelts xpShift (addInt (off xpShift) oneZ)
           in
           (maxCase : Bool) →
           andWordFlag64 x1 dh nx0 dl maxCase →
           IfSet
             maxCase
             (MaxQuotientBranch sx sy i nextI mdn
               originalX baseX originalQ divisor
               xState qState xpShift qp xd qh dh dl vy)
             (SmallQuotientBranch sx sy i nextI mdn
               originalX baseX originalQ divisor
               xState qState xpShift qp xd
               qh x1 dh dl v vy nx0)))))

  QuotientWrite :
    {Zone : Set} →
    Word32 → Word32 → Word32 → Word32 → Word32 →
    Ptr Zone Word64 → Ptr Zone Word64 →
    Ptr Zone Word64 → Ptr Zone Word64 →
    Ptr Zone Word64 → Ptr Zone Word64 →
    Word64 → Word64 → Word64 → Word64 → Int → Word64 → Set
  QuotientWrite sx sy oldI nextI mdn originalX originalQ
    xState qState xp qp qh x1 dh dl vy quotient =
    cursorAt qp (addInt (off qp) (negative 1))
    ∧
    ((qShift : Ptr _ Word64) →
      shiftedBy qShift qp (negative 1) →
      let lower = addInt (off qShift) oneZ
          upper =
            addInt (off qShift)
              (subtractInt
                (subtractInt (signed32 sx) (signed32 sy))
                (signed32 nextI))
          index = off qShift
          old = pelts qState
      in
      (lower ≤Z upper ∧ (index <Z lower ∨ upper ≤Z index))
      ∧
      (valueSub old lower upper
         ≡ valueSub (update old index quotient) lower upper →
       (accessAt qShift index ∧ writeable qShift ≡ true)
       ∧
       ((storedQ nextQ : Ptr _ Word64) →
         aliasThrough storedQ nextQ qShift →
         aliasThrough storedQ nextQ qShift →
         sameStateShape nextQ qState →
         pelts storedQ ≡ update (pelts qShift) (off storedQ) quotient →
         signed32 nextI <Z signed32 oldI
         ∧ loopInvariant sx sy nextI mdn originalX originalQ
             xState nextQ xp storedQ qh x1 dh dl vy)))

  MaxQuotientBranch :
    {Zone : Set} →
    Word32 → Word32 → Word32 → Word32 → Word32 →
    Ptr Zone Word64 → Ptr Zone Word64 →
    Ptr Zone Word64 → Ptr Zone Word64 →
    Ptr Zone Word64 → Ptr Zone Word64 → Ptr Zone Word64 →
    Ptr Zone Word64 → Ptr Zone Word64 →
    Word64 → Word64 → Word64 → Int → Set
  MaxQuotientBranch sx sy oldI nextI mdn
    originalX baseX originalQ divisor
    xState qState xp qp xd qh dh dl vy =
    let estimate =
          addInt
            (valueSub (pelts xd)
              (addInt (off xd) oneZ)
              (subtractInt
                (addInt (off xd) (signed32 sy))
                oneZ))
            (addInt
              (multiplyInt
                (powerInt radixZ
                  (subtractInt (signed32 sy) twoZ))
                (unsignedZ dl))
              (multiplyInt
                (powerInt radixZ
                  (subtractInt (signed32 sy) oneZ))
                (unsignedZ dh)))
          <Z vy
    in
    estimate
    ∧
    (estimate →
     (xc : List Word64) →
     copyOf xc (pelts xState) (cellCount xState) →
     (valid divisor (signed32 sy)
      ∧ valid xd (signed32 sy)
      ∧ writeable xd ≡ true)
     ∧
     ((xd2 xp2 x3 : Ptr _ Word64) →
       aliasThrough xd2 x3 xd →
       aliasThrough xp2 x3 xp →
       sameStateShape x3 xState →
       (borrow : Word64) →
       submulEffect xd2 xd (off xd) divisor
         (signed32 sy) max64 borrow →
       value x3 (signed32 nextI) ≡ value xState (signed32 nextI)
       ∧
       (value x3 (signed32 nextI) ≡ value xState (signed32 nextI) →
        let lower = off x3
            middle = off xd2
            upper =
              subtractInt
                (addInt
                  (addInt (off x3) (signed32 sy))
                  (signed32 nextI))
                oneZ
            m = pelts x3
        in
        (lower ≤Z middle ∧ middle ≤Z upper)
        ∧
        (valueSub m lower upper
           ≡ addInt
               (valueSub m lower middle)
               (multiplyInt
                 (valueSub m middle upper)
                 (powerInt radixZ
                   (subtractInt middle lower))) →
         QuotientWrite sx sy oldI nextI mdn originalX originalQ
           x3 qState xp2 qp qh
           (pelts xp2 (addInt (off xp2) oneZ))
           dh dl vy max64))))

  SmallQuotientBranch :
    {Zone : Set} →
    Word32 → Word32 → Word32 → Word32 → Word32 →
    Ptr Zone Word64 → Ptr Zone Word64 →
    Ptr Zone Word64 → Ptr Zone Word64 →
    Ptr Zone Word64 → Ptr Zone Word64 → Ptr Zone Word64 →
    Ptr Zone Word64 → Ptr Zone Word64 →
    Word64 → Word64 → Word64 → Word64 → Word64 → Int →
    Word64 → Set
  SmallQuotientBranch sx sy oldI nextI mdn
    originalX baseX originalQ divisor
    xState qState xp qp xd qh oldX1 dh dl v vy nx0 =
    addInt (unsignedZ nx0)
      (multiplyInt radixZ (unsignedZ oldX1))
      <Z addInt (unsignedZ dl)
          (multiplyInt radixZ (unsignedZ dh))
    ∧ accessAt xp (off xp)
    ∧ accessAt xp (addInt (off xp) oneZ)
    ∧
    (let xp0 = pelts xp (off xp)
         xp1 = pelts xp (addInt (off xp) oneZ)
         vlx = value xd (subtractInt (signed32 sy) twoZ)
         decomposition =
           value xd (signed32 sy)
             ≡ addInt vlx
                 (multiplyInt
                   (powerInt radixZ
                     (subtractInt (signed32 sy) twoZ))
                   (addInt
                     (unsignedZ xp0)
                     (multiplyInt radixZ (unsignedZ xp1))))
     in
     decomposition
     ∧
     (decomposition →
      (halfRadixZ ≤Z unsignedZ dh ∧ reciprocal3by2 v dh dl
       ∧ addInt (unsignedZ xp1)
           (multiplyInt radixZ (unsignedZ oldX1))
         <Z addInt (unsignedZ dl)
             (multiplyInt radixZ (unsignedZ dh)))
      ∧
      ((qu rl rh : Word64) →
        div3by2Result qu rl rh oldX1 xp1 xp0 dh dl v →
        SmallAfterEstimate sx sy oldI nextI mdn
          originalX baseX originalQ divisor
          xState qState xp qp xd qh oldX1 dh dl vy qu rl rh)))

  SmallAfterEstimate :
    {Zone : Set} →
    Word32 → Word32 → Word32 → Word32 → Word32 →
    Ptr Zone Word64 → Ptr Zone Word64 →
    Ptr Zone Word64 → Ptr Zone Word64 →
    Ptr Zone Word64 → Ptr Zone Word64 → Ptr Zone Word64 →
    Ptr Zone Word64 → Ptr Zone Word64 →
    Word64 → Word64 → Word64 → Word64 → Int →
    Word64 → Word64 → Word64 → Set
  SmallAfterEstimate sx sy oldI nextI mdn
    originalX baseX originalQ divisor
    xState qState xp qp xd qh oldX1 dh dl vy qu rl rh =
    let lower = off xState
        middle = off xd
        upper =
          subtractInt
            (addInt
              (addInt (off xState) (signed32 sy))
              (signed32 oldI))
            oneZ
        m = pelts xState
    in
    (lower ≤Z middle ∧ middle ≤Z upper)
    ∧
    (valueSub m lower upper
       ≡ addInt
           (valueSub m lower middle)
           (multiplyInt
             (valueSub m middle upper)
             (powerInt radixZ (subtractInt middle lower))) →
     (xc : List Word64) →
     copyOf xc (pelts xState) (cellCount xState) →
     int32InBounds (subtractInt (signed32 sy) twoZ)
     ∧
     ((subSize : Word32) →
       signed32 subSize ≡ subtractInt (signed32 sy) twoZ →
       (valid divisor (signed32 subSize)
        ∧ valid xd (signed32 subSize)
        ∧ writeable xd ≡ true)
       ∧
       ((xd2 xp2 x3 : Ptr _ Word64) →
         aliasThrough xd2 x3 xd →
         aliasThrough xp2 x3 xp →
         sameStateShape x3 xState →
         (cy : Word64) →
         submulEffect xd2 xd (off xd) divisor
           (signed32 subSize) qu cy →
         value x3 (signed32 nextI) ≡ value xState (signed32 nextI)
         ∧
         (value x3 (signed32 nextI) ≡ value xState (signed32 nextI) →
          (cy1 : Word64) →
          IfSet
            (intLess (unsignedZ rl) (unsignedZ cy))
            (cy1 ≡ one64)
            (cy1 ≡ zero64) →
          (newLow : Word64) →
          unsignedZ newLow ≡
            euclideanModuloPositive
              (subtractInt (unsignedZ rl) (unsignedZ cy))
              radixNat →
          (cy2 : Word64) →
          IfSet
            (intLess (unsignedZ rh) (unsignedZ cy1))
            (cy2 ≡ one64)
            (cy2 ≡ zero64) →
          (newHigh : Word64) →
          unsignedZ newHigh ≡
            euclideanModuloPositive
              (subtractInt (unsignedZ rh) (unsignedZ cy1))
              radixNat →
          let updateIndex = off xp2
              old = pelts x3
              updated = update old updateIndex newLow
              xdUpper =
                subtractInt
                  (addInt (off xd2) (signed32 sy))
                  oneZ
              prefixUpper = addInt (off x3) (signed32 nextI)
              shortUpper =
                subtractInt
                  (addInt (off xd2) (signed32 sy))
                  twoZ
          in
          (off xd2 ≤Z updateIndex ∧ updateIndex <Z xdUpper)
          ∧
          (valueSub updated (off xd2) xdUpper
             ≡ addInt
                 (valueSub old (off xd2) xdUpper)
                 (multiplyInt
                   (powerInt radixZ
                     (subtractInt updateIndex (off xd2)))
                   (subtractInt
                     (unsignedZ newLow)
                     (unsignedZ (old updateIndex)))) →
           (off x3 ≤Z prefixUpper
            ∧ (updateIndex <Z off x3 ∨ prefixUpper ≤Z updateIndex))
           ∧
           (valueSub old (off x3) prefixUpper
              ≡ valueSub updated (off x3) prefixUpper →
            (off xd2 ≤Z shortUpper
             ∧ (updateIndex <Z off xd2 ∨ shortUpper ≤Z updateIndex))
            ∧
            (valueSub old (off xd2) shortUpper
               ≡ valueSub updated (off xd2) shortUpper →
             (accessAt xp2 updateIndex ∧ writeable xp2 ≡ true)
             ∧
             ((xd3 xp3 x4 : Ptr _ Word64) →
               aliasThrough xp3 x4 xp2 →
               aliasThrough xd3 x4 xd2 →
               aliasThrough xp3 x4 xp2 →
               sameStateShape x4 x3 →
               pelts xp3 ≡ update (pelts xp2) (off xp3) newLow →
               let relation =
                     subtractInt
                       (addInt
                         (value xd3
                           (subtractInt (signed32 sy) oneZ))
                         (multiplyInt
                           (powerInt radixZ
                             (subtractInt (signed32 sy) oneZ))
                           (unsignedZ newHigh)))
                       (multiplyInt
                         (powerInt radixZ (signed32 sy))
                         (unsignedZ cy2))
                     ≡ subtractInt
                         (addInt
                           (value xd (signed32 sy))
                           (multiplyInt
                             (powerInt radixZ (signed32 sy))
                             (unsignedZ oldX1)))
                         (multiplyInt (unsignedZ qu) vy)
               in
               relation
               ∧
               (relation →
                (zeroCarry : Bool) →
                wordFlag64 cy2 zero64 zeroCarry →
                IfSet
                  zeroCarry
                  (QuotientWrite sx sy oldI nextI mdn
                    originalX originalQ x4 qState xp3 qp
                    qh newHigh dh dl vy qu)
                  (CorrectionBranch sx sy oldI nextI mdn
                    originalX baseX originalQ divisor
                    x4 qState xp3 qp xd3
                    qh qu newHigh dh dl vy))))))))))

  CorrectionBranch :
    {Zone : Set} →
    Word32 → Word32 → Word32 → Word32 → Word32 →
    Ptr Zone Word64 → Ptr Zone Word64 →
    Ptr Zone Word64 → Ptr Zone Word64 →
    Ptr Zone Word64 → Ptr Zone Word64 → Ptr Zone Word64 →
    Ptr Zone Word64 → Ptr Zone Word64 →
    Word64 → Word64 → Word64 → Word64 → Word64 → Int → Set
  CorrectionBranch sx sy oldI nextI mdn
    originalX baseX originalQ divisor
    xState qState xp qp xd qh qu oldHigh dh dl vy =
    zeroZ <Z unsignedZ qu
    ∧
    (zeroZ <Z unsignedZ qu →
     subtractInt (powerInt radixZ (signed32 sy)) vy
       ≤Z addInt
           (value xd (subtractInt (signed32 sy) oneZ))
           (multiplyInt
             (powerInt radixZ
               (subtractInt (signed32 sy) oneZ))
             (unsignedZ oldHigh))
     ∧
     (subtractInt (powerInt radixZ (signed32 sy)) vy
        ≤Z addInt
            (value xd (subtractInt (signed32 sy) oneZ))
            (multiplyInt
              (powerInt radixZ
                (subtractInt (signed32 sy) oneZ))
              (unsignedZ oldHigh)) →
      (xc1 : List Word64) →
      copyOf xc1 (pelts xState) (cellCount xState) →
      int32InBounds (subtractInt (signed32 sy) oneZ)
      ∧
      ((addSize : Word32) →
        signed32 addSize ≡ subtractInt (signed32 sy) oneZ →
        (valid xd (signed32 addSize)
         ∧ valid divisor (signed32 addSize)
         ∧ writeable xd ≡ true)
        ∧
        ((xd4 xp4 x5 : Ptr _ Word64) →
          aliasThrough xd4 x5 xd →
          aliasThrough xp4 x5 xp →
          sameStateShape x5 xState →
          (carry : Word64) →
          addEffect xd4 xd (off xd) divisor
            (signed32 addSize) carry →
          value x5 (signed32 nextI) ≡ value xState (signed32 nextI)
          ∧
          (value x5 (signed32 nextI) ≡ value xState (signed32 nextI) →
           Not (radixZ ≡ zeroZ)
           ∧
           ((dhPlusCarry : Word64) →
             unsignedZ dhPlusCarry ≡
               euclideanModuloPositive
                 (addInt (unsignedZ dh) (unsignedZ carry))
                 radixNat →
             (newHigh : Word64) →
             unsignedZ newHigh ≡
               euclideanModuloPositive
                 (addInt
                   (unsignedZ oldHigh)
                   (unsignedZ dhPlusCarry))
                 radixNat →
             addInt
               (value xd4
                 (subtractInt (signed32 sy) oneZ))
               (multiplyInt
                 (powerInt radixZ
                   (subtractInt (signed32 sy) oneZ))
                 (unsignedZ newHigh))
               ≡ subtractInt
                   (addInt
                     (value xd
                       (subtractInt (signed32 sy) oneZ))
                     (addInt
                       (multiplyInt
                         (powerInt radixZ
                           (subtractInt (signed32 sy) oneZ))
                         (unsignedZ oldHigh))
                       vy))
                   (powerInt radixZ (signed32 sy)))
           ∧
           ((newHigh : Word64) →
             addInt
               (value xd4
                 (subtractInt (signed32 sy) oneZ))
               (multiplyInt
                 (powerInt radixZ
                   (subtractInt (signed32 sy) oneZ))
                 (unsignedZ newHigh))
               ≡ subtractInt
                   (addInt
                     (value xd
                       (subtractInt (signed32 sy) oneZ))
                     (addInt
                       (multiplyInt
                         (powerInt radixZ
                           (subtractInt (signed32 sy) oneZ))
                         (unsignedZ oldHigh))
                       vy))
                   (powerInt radixZ (signed32 sy)) →
             uint64InBounds (subtractInt (unsignedZ qu) oneZ)
             ∧
             ((correctedQu : Word64) →
               unsignedZ correctedQu
                 ≡ subtractInt (unsignedZ qu) oneZ →
               QuotientWrite sx sy oldI nextI mdn
                 originalX originalQ x5 qState xp4 qp
                 qh newHigh dh dl vy correctedQu)))))))

LoopStartWithDivisor :
  {Zone : Set} →
  Word32 → Word32 → Word32 → Word32 →
  Ptr Zone Word64 → Ptr Zone Word64 →
  Ptr Zone Word64 → Ptr Zone Word64 →
  Ptr Zone Word64 → Ptr Zone Word64 →
  Ptr Zone Word64 → Ptr Zone Word64 →
  Word64 → Word64 → Word64 → Word64 → Word64 → Int → Set
LoopStartWithDivisor sx sy i mdn originalX baseX originalQ divisor
  xState qState xp qp qh x1 dh dl v vy =
  loopInvariant sx sy i mdn originalX originalQ
    xState qState xp qp qh x1 dh dl vy
  ∧ AllLoopStates sx sy mdn originalX baseX originalQ divisor
      qh dh dl v vy

PreAdjust :
  {Zone : Set} →
  Word32 → Word32 → Word32 → Word32 →
  Ptr Zone Word64 → Ptr Zone Word64 → Ptr Zone Word64 →
  Ptr Zone Word64 → Ptr Zone Word64 → Ptr Zone Word64 →
  Word64 → Word64 → Word64 → Word64 → Int → Set
PreAdjust sx sy i mdn originalX divisor initialQ xp qp xd
  qh dh dl v vy =
  (zeroFlag : Bool) →
  wordFlag64 qh zero64 zeroFlag →
  (zeroFlag ≡ false →
    zeroZ ≤Z signed32 sy
    ∧ valid xd (signed32 sy)
    ∧ valid divisor (signed32 sy)
    ∧ writeable xd ≡ true)
  ∧
  ((xState xpState : Ptr _ Word64) →
    Exists Bool
      (λ branchFlag →
        wordFlag64 qh zero64 branchFlag
        ∧ IfSet
            branchFlag
            (xState ≡ originalX ∧ xpState ≡ xp)
            (Exists (Ptr _ Word64)
              (λ xdState →
                aliasThrough xdState xState xd
                ∧ aliasThrough xpState xState xp
                ∧ sameStateShape xState originalX
                ∧ Exists Word64
                    (λ borrow →
                      initialSubmulEffect xdState xd (off xd) divisor
                        (signed32 sy) one64 borrow)))) →
    accessAt xpState (addInt (off xpState) oneZ)
    ∧
    LoopStartWithDivisor sx sy i mdn
      originalX xState initialQ divisor
      xState initialQ xpState qp qh
      (pelts xpState (addInt (off xpState) oneZ))
      dh dl v vy)

InitialSetup :
  {Zone : Set} →
  Word32 → Word32 →
  Ptr Zone Word64 → Ptr Zone Word64 → Ptr Zone Word64 → Set
InitialSetup sy sx x y q =
  int32InBounds (subtractInt (signed32 sx) twoZ)
  ∧
  ((xpAmount : Word32) →
    signed32 xpAmount ≡ subtractInt (signed32 sx) twoZ →
    cursorAt x (addInt (off x) (signed32 xpAmount))
    ∧
    ((xp : Ptr _ Word64) →
      shiftedBy xp x (signed32 xpAmount) →
      int32InBounds
        (subtractInt (signed32 sx) (signed32 sy))
      ∧
      ((i : Word32) →
        signed32 i ≡
          subtractInt (signed32 sx) (signed32 sy) →
        cursorAt q (addInt (off q) (signed32 i))
        ∧
        ((qp : Ptr _ Word64) →
          shiftedBy qp q (signed32 i) →
          int32InBounds
            (subtractInt (signed32 sy) oneZ)
          ∧
          ((highIndex : Word32) →
            signed32 highIndex ≡
              subtractInt (signed32 sy) oneZ →
            accessAt y (addInt (off y) (signed32 highIndex))
            ∧
            (let dh =
                   pelts y (addInt (off y) (signed32 highIndex))
             in
             int32InBounds
               (subtractInt (signed32 sy) twoZ)
             ∧
             ((lowIndex : Word32) →
               signed32 lowIndex ≡
                 subtractInt (signed32 sy) twoZ →
               accessAt y (addInt (off y) (signed32 lowIndex))
               ∧
               (let dl =
                      pelts y
                        (addInt (off y) (signed32 lowIndex))
                in
                halfRadixZ ≤Z unsignedZ dh
                ∧
                ((v : Word64) →
                  reciprocal3by2 v dh dl →
                  int32InBounds
                    (subtractInt
                      (signed32 sx) (signed32 sy))
                  ∧
                  ((iAgain : Word32) →
                    signed32 iAgain ≡
                      subtractInt
                        (signed32 sx) (signed32 sy) →
                    int32InBounds
                      (subtractInt twoZ (signed32 sy))
                    ∧
                    ((mdn : Word32) →
                      signed32 mdn ≡
                        subtractInt twoZ (signed32 sy) →
                      cursorAt xp
                        (addInt (off xp) (signed32 mdn))
                      ∧
                      ((xd : Ptr _ Word64) →
                        shiftedBy xd xp (signed32 mdn) →
                        let vy = value y (signed32 sy)
                        in
                        (valid xd (signed32 sy)
                         ∧ valid y (signed32 sy))
                        ∧
                        ((r : Word32) →
                          signed32 r ≡
                            compareInt
                              (value xd (signed32 sy))
                              (value y (signed32 sy)) →
                          ((qh : Word64) →
                            IfSet
                              (intLessOrEqual
                                zeroZ (signed32 r))
                              (qh ≡ one64)
                              (qh ≡ zero64) →
                            PreAdjust sx sy iAgain mdn
                              x y q xp qp xd
                              qh dh dl v vy))))))))))))))

div-sb-qr'vc : Set₁
div-sb-qr'vc =
  (Zone : Set) →
  (sy sx : Word32) →
  (x y q : Ptr Zone Word64) →
  threeZ ≤Z signed32 sy →
  signed32 sy ≤Z signed32 sx →
  valid x (signed32 sx) →
  valid y (signed32 sy) →
  valid q
    (subtractInt (signed32 sx) (signed32 sy)) →
  writeable q ≡ true →
  writeable x ≡ true →
  normalized y sy →
  InitialSetup sy sx x y q
