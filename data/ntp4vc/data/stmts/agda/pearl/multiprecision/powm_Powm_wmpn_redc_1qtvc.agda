-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/powm_Powm_wmpn_redc_1qtvc: the verification condition
-- for one-limb Montgomery reduction, including its multiprecision loop
-- invariants, pointer-frame obligations, carry handling, and modular result.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module powm_Powm_wmpn_redc_1qtvc where

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

zeroZ oneZ twoZ max32Z radixZ : Int
zeroZ = pos 0
oneZ = pos 1
twoZ = pos 2
max32Z = pos 2147483647
radixZ = pos 18446744073709551616

min32Z : Int
min32Z = negsuc 2147483647

radixNat : Nat
radixNat = 18446744073709551616

int32InBounds : Int → Set
int32InBounds value =
  min32Z ≤Z value ∧ value ≤Z max32Z

odd : Int → Set
odd value = moduloInt value twoZ ≡ oneZ

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
redc ur u n modulus =
  moduloInt ur modulus ≡
    moduloInt
      (multiplyInt (powerZ radixNat n) u)
      modulus

updateInt :
  (Int → Word64) →
  Int →
  Word64 →
  Int →
  Word64
updateInt old index new query with intEqual query index
... | true = new
... | false = old query

PeltsEqual :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Set
PeltsEqual first second =
  (index : Int) → pelts first index ≡ pelts second index

PeltsUpdated :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Int →
  Word64 →
  Set
PeltsUpdated newer older index new =
  (query : Int) →
  pelts newer query ≡ updateInt (pelts older) index new query

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

pairedFrame :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Set
pairedFrame first second original =
  contents first ≡ contents second
  ∧ listLength (contents second) ≡ listLength (contents original)
  ∧ off first ≡ off original
  ∧ lo first ≡ lo original
  ∧ hi first ≡ hi original
  ∧ writeable first ≡ writeable original
  ∧ region first ≡ region original

loopEquation :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Int →
  Int →
  Int →
  Int →
  Set
loopEquation originalUp current currentUp n vm index added =
  addInt
    (multiplyInt
      (powerZ radixNat index)
      (value current
        (subtractInt (addInt n n) index)))
    (multiplyInt
      (powerZ radixNat n)
      (value currentUp index))
  ≡
  addInt
    (value originalUp (addInt n n))
    (multiplyInt vm added)

loopModulo :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Int →
  Int →
  Int →
  Set
loopModulo originalUp current currentUp n vm index =
  moduloInt
    (addInt
      (multiplyInt
        (powerZ radixNat index)
        (value current
          (subtractInt (addInt n n) index)))
      (multiplyInt
        (powerZ radixNat n)
        (value currentUp index)))
    vm
  ≡ moduloInt (value originalUp (addInt n n)) vm

loopState :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Int →
  Int →
  Int →
  Int →
  Set
loopState originalUp current currentUp n vm index added =
  off current ≡ addInt (off currentUp) index
  ∧ PeltsEqual current currentUp
  ∧ lo current ≡ lo currentUp
  ∧ hi current ≡ hi currentUp
  ∧ plength current ≡ plength currentUp
  ∧ writeable current ≡ true
  ∧ loopEquation originalUp current currentUp n vm index added
  ∧ (zeroZ ≤Z added ∧ added <Z powerZ radixNat index)
  ∧ loopModulo originalUp current currentUp n vm index

addmulResult :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word64 →
  Word64 →
  Set
addmulResult u1 u mp n m o4 =
  addInt
    (value u1 (signed32 n))
    (multiplyInt
      (powerZ radixNat (signed32 n))
      (unsignedZ o4))
  ≡
  addInt
    (value u (signed32 n))
    (multiplyInt
      (value mp (signed32 n))
      (unsignedZ m))
  ∧ outsideUnchanged u1 u (signed32 n)

nextLoopState :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word32 →
  Word64 →
  Int →
  Int →
  Set
nextLoopState originalUp o5 up3 n j m vm added =
  let next = addInt (signed32 j) oneZ
      nextAdded =
        addInt
          added
          (multiplyInt
            (unsignedZ m)
            (powerZ radixNat (signed32 j)))
  in
  off o5 ≡ addInt (off up3) next
  ∧ PeltsEqual o5 up3
  ∧ lo o5 ≡ lo up3
  ∧ hi o5 ≡ hi up3
  ∧ plength o5 ≡ plength up3
  ∧ writeable o5 ≡ true
  ∧ loopEquation
      originalUp o5 up3 (signed32 n) vm next nextAdded
  ∧ (zeroZ ≤Z nextAdded
     ∧ nextAdded <Z powerZ radixNat next)
  ∧ loopModulo
      originalUp o5 up3 (signed32 n) vm next

afterStoredLimb :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word32 →
  Word64 →
  Int →
  Int →
  Set
afterStoredLimb originalUp u2 up3 n j m vm added =
  (lo u2 ≤Z addInt (off u2) oneZ
   ∧ addInt (off u2) oneZ ≤Z hi u2)
  ∧
  ((o5 : Ptr _) →
    shiftedState o5 u2 oneZ →
    nextLoopState originalUp o5 up3 n j m vm added)

afterAddmul :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word32 →
  Word64 →
  Word64 →
  Int →
  Int →
  Set
afterAddmul originalUp u1 up2 up1 n j m o4 vm added =
  ((lo u1 ≤Z off u1 ∧ off u1 <Z hi u1)
   ∧ writeable u1 ≡ true)
  ∧
  ((u2 up3 : Ptr _) →
    pairedFrame u2 up3 u1 →
    pairedFrame u2 up3 u1 →
    sameFrame up3 up2 →
    PeltsUpdated u2 u1 (off u2) o4 →
    afterStoredLimb originalUp u2 up3 n j m vm added)

afterNnj :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word32 →
  Word64 →
  Int →
  Int →
  Set
afterNnj originalUp mp u up1 n j m vm added =
  (valid mp (signed32 n)
   ∧ valid u (signed32 n)
   ∧ writeable u ≡ true)
  ∧
  ((u1 up2 : Ptr _) →
    pairedFrame u1 up2 u →
    pairedFrame u1 up2 u →
    sameFrame up2 up1 →
    (o4 : Word64) →
    addmulResult u1 u mp n m o4 →
    afterAddmul originalUp u1 up2 up1 n j m o4 vm added)

afterMultiplier :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word32 →
  Word64 →
  Int →
  Int →
  Set
afterMultiplier originalUp mp u up1 n j m vm added =
  int32InBounds (addInt (signed32 n) (signed32 n))
  ∧
  ((o3 : Word32) →
    signed32 o3 ≡ addInt (signed32 n) (signed32 n) →
    int32InBounds (subtractInt (signed32 o3) (signed32 j))
    ∧
    ((nnj : Word32) →
      signed32 nnj ≡ subtractInt (signed32 o3) (signed32 j) →
      afterNnj originalUp mp u up1 n j m vm added))

loopIterationConclusion :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word32 →
  Word64 →
  Int →
  Int →
  Set
loopIterationConclusion originalUp mp u up1 n j invm vm added =
  (lo u ≤Z off u ∧ off u <Z hi u)
  ∧
  ((m : Word64) →
    unsignedZ m ≡
      moduloInt
        (multiplyInt
          (unsignedZ (pelts u (off u)))
          (unsignedZ invm))
        radixZ →
    afterMultiplier originalUp mp u up1 n j m vm added)

carryModulo :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word64 →
  Int →
  Set
carryModulo result prior originalUp n carry vm =
  moduloInt (value result (signed32 n)) vm ≡
    moduloInt
      (addInt
        (value prior (signed32 n))
        (multiplyInt
          (powerZ radixNat (signed32 n))
          (unsignedZ carry)))
      vm
  ∧ outsideUnchanged result prior (signed32 n)
  ∧
  (value originalUp
      (multiplyInt twoZ (signed32 n))
    <Z
    multiplyInt
      (powerZ radixNat (signed32 n))
      vm →
   value result (signed32 n) <Z multiplyInt twoZ vm)

subtractPremise :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word64 →
  Set
subtractPremise rp2 rp1 mp n b =
  subtractInt
    (value rp2 (signed32 n))
    (multiplyInt
      (powerZ radixNat (signed32 n))
      (unsignedZ b))
  ≡ subtractInt
      (value rp1 (signed32 n))
      (value mp (signed32 n))
  ∧ (zeroZ ≤Z unsignedZ b ∧ unsignedZ b ≤Z oneZ)
  ∧ outsideUnchanged rp2 rp1 (signed32 n)

subtractBranch :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word64 →
  Int →
  Set
subtractBranch originalUp mp rp1 originalRp n carry vm =
  (zeroZ ≤Z signed32 n
   ∧ valid rp1 (signed32 n)
   ∧ valid mp (signed32 n)
   ∧ writeable rp1 ≡ true)
  ∧
  ((rp2 : Ptr _) →
    sameFrame rp2 rp1 →
    (b : Word64) →
    subtractPremise rp2 rp1 mp n b →
    carryModulo rp2 rp1 originalUp n carry vm)

noSubtractBranch :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word64 →
  Int →
  Set
noSubtractBranch originalUp rp1 n carry vm =
  moduloInt (value rp1 (signed32 n)) vm ≡
    moduloInt
      (addInt
        (value rp1 (signed32 n))
        (multiplyInt
          (powerZ radixNat (signed32 n))
          (unsignedZ carry)))
      vm
  ∧
  (value originalUp
      (multiplyInt twoZ (signed32 n))
    <Z
    multiplyInt
      (powerZ radixNat (signed32 n))
      vm →
   value rp1 (signed32 n) <Z multiplyInt twoZ vm)

carryFlag :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word64 →
  Int →
  Set
carryFlag originalUp mp rp1 originalRp n carry vm =
  (flag : Bool) →
  ((unsignedZ carry ≡ unsignedZ zero64 → flag ≡ true)
   ∧ (flag ≡ true → carry ≡ zero64)) →
  IfSet
    (notBool flag)
    (subtractBranch originalUp mp rp1 originalRp n carry vm)
    (noSubtractBranch originalUp rp1 n carry vm)

finalReductionPremise :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word64 →
  Int →
  Set
finalReductionPremise result prior originalUp n carry vm =
  carryModulo result prior originalUp n carry vm

finalReductionConclusion :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Int →
  Set
finalReductionConclusion result originalRp originalUp mp n vm =
  redc
    (value originalUp (multiplyInt twoZ (signed32 n)))
    (value result (signed32 n))
    (signed32 n)
    (value mp (signed32 n))
  ∧ outsideUnchanged result originalRp (signed32 n)
  ∧
  (value originalUp
      (multiplyInt twoZ (signed32 n))
    <Z
    multiplyInt
      (powerZ radixNat (signed32 n))
      (value mp (signed32 n)) →
   value result (signed32 n)
     <Z multiplyInt twoZ (value mp (signed32 n)))

afterRp1 :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Int →
  Set
afterRp1 base shifted originalUp mp originalRp n vm =
  (rp1 : Ptr _) →
  sameFrame rp1 originalRp →
  (carry : Word64) →
  ((zeroZ ≤Z unsignedZ carry ∧ unsignedZ carry ≤Z oneZ)
   ∧
   addInt
     (value rp1 (signed32 n))
     (multiplyInt
       (powerZ radixNat (signed32 n))
       (unsignedZ carry))
   ≡ addInt
       (value base (signed32 n))
       (value shifted (signed32 n))
   ∧ outsideUnchanged rp1 originalRp (signed32 n)) →
  carryFlag originalUp mp rp1 originalRp n carry vm
  ∧
  ((rp2 : Ptr _) →
    sameFrame rp2 rp1 →
    finalReductionPremise rp2 rp1 originalUp n carry vm →
    finalReductionConclusion rp2 originalRp originalUp mp n vm)

afterShiftedBase :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Int →
  Set
afterShiftedBase base shifted originalUp mp originalRp n vm =
  (valid base (signed32 n)
   ∧ valid shifted (signed32 n)
   ∧ valid originalRp (signed32 n)
   ∧ writeable originalRp ≡ true)
  ∧ afterRp1 base shifted originalUp mp originalRp n vm

negativeShiftConclusion :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Int →
  Set
negativeShiftConclusion base originalUp mp originalRp n vm =
  let back = negateInt (signed32 n)
  in
  int32InBounds back
  ∧
  ((o3 : Word32) →
    signed32 o3 ≡ back →
    (lo base ≤Z addInt (off base) (signed32 o3)
     ∧ addInt (off base) (signed32 o3) ≤Z hi base)
    ∧
    ((shiftedOnce : Ptr _) →
      shiftedState shiftedOnce base (signed32 o3) →
      int32InBounds back
      ∧
      ((o4 : Word32) →
        signed32 o4 ≡ back →
        (lo base ≤Z addInt (off base) (signed32 o4)
         ∧ addInt (off base) (signed32 o4) ≤Z hi base)
        ∧
        ((shiftedTwice : Ptr _) →
          shiftedState shiftedTwice base (signed32 o4) →
          afterShiftedBase
            base shiftedTwice originalUp mp originalRp n vm))))

loopExitState :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word32 →
  Int →
  Int →
  Set
loopExitState originalUp u up1 n o2 vm added =
  loopState
    originalUp u up1 (signed32 n) vm
    (addInt (signed32 o2) oneZ) added

loopObligations :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word32 →
  Word64 →
  Int →
  Int →
  Set
loopObligations originalUp mp originalRp u up1 n o2 invm vm added =
  (j : Word32) →
  let j1 = signed32 j
  in
  (((zeroZ ≤Z j1 ∧ j1 ≤Z signed32 o2)
    ∧ loopState originalUp u up1 (signed32 n) vm j1 added) →
   loopIterationConclusion
     originalUp mp u up1 n j invm vm added)
  ∧
  (loopExitState originalUp u up1 n o2 vm added →
   negativeShiftConclusion
     u originalUp mp originalRp n vm)

afterInitialState :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word32 →
  Word64 →
  Int →
  Set
afterInitialState originalUp mp originalRp o1 n o2 invm vm =
  (zeroZ ≤Z addInt (signed32 o2) oneZ →
    loopState originalUp o1 originalUp
      (signed32 n) vm zeroZ zeroZ
    ∧
    ((added : Int) →
      (u up1 : Ptr _) →
      sameFrame up1 originalUp →
      loopObligations
        originalUp mp originalRp u up1 n o2 invm vm added))
  ∧
  (addInt (signed32 o2) oneZ <Z zeroZ →
    negativeShiftConclusion
      o1 originalUp mp originalRp n vm)

afterO1 :
  {Zone : Set} →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Ptr Zone →
  Word32 →
  Word64 →
  Set
afterO1 originalUp mp originalRp o1 n invm =
  let vm = value mp (signed32 n)
  in
  int32InBounds (subtractInt (signed32 n) oneZ)
  ∧
  ((o2 : Word32) →
    signed32 o2 ≡ subtractInt (signed32 n) oneZ →
    afterInitialState
      originalUp mp originalRp o1 n o2 invm vm)

wmpn-redc-1'vc : Set₁
wmpn-redc-1'vc =
  (Zone : Set) →
  (n : Word32) →
  (mp up rp : Ptr Zone) →
  (invm : Word64) →
  zeroZ <Z signed32 n →
  valid mp (signed32 n) →
  valid up (multiplyInt twoZ (signed32 n)) →
  valid rp (signed32 n) →
  odd (value mp (signed32 n)) →
  moduloInt
    (multiplyInt
      (value mp (signed32 n))
      (unsignedZ invm))
    radixZ
    ≡ subtractInt radixZ oneZ →
  writeable up ≡ true →
  writeable rp ≡ true →
  lo up ≤Z addInt (off up) zeroZ
  ∧ addInt (off up) zeroZ ≤Z hi up
  ∧
  ((o1 : Ptr _) →
    shiftedState o1 up zeroZ →
    afterO1 up mp rp o1 n invm)
