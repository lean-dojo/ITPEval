-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/div_Div_div3by2_invqtvc: the verification condition
-- for reciprocal-based division of a three-limb unsigned integer by a
-- normalized two-limb 64-bit divisor, including quotient correction and
-- two-limb remainder bounds. This file contains no proof.

{-# OPTIONS --safe #-}

module div_Div_div3by2_invqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; div-helper)

infix 4 _≤Z_ _<Z_
infixr 5 _∷V_
infixr 3 _∧_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

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

IfBool : Bool → Bool → Bool → Bool
IfBool true when-true when-false = when-true
IfBool false when-true when-false = when-false

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

Word64 : Set
Word64 = Vec Bool 64

zeroZ oneZ radixZ max64Z halfRadixZ : Int
zeroZ = pos 0
oneZ = pos 1
radixZ = pos 18446744073709551616
max64Z = pos 18446744073709551615
halfRadixZ = pos 9223372036854775808

radixNat reciprocal3NumeratorNat : Nat
radixNat = 18446744073709551616
reciprocal3NumeratorNat =
  radixNat * radixNat * radixNat - 1

divisorNat : Word64 → Word64 → Nat
divisorNat dh dl =
  unsignedNat dl + radixNat * unsignedNat dh

reciprocal3by2 : Word64 → Word64 → Word64 → Set
reciprocal3by2 v dh dl =
  unsignedZ v ≡
  subtractInt
    (pos (natDivide reciprocal3NumeratorNat (divisorNat dh dl)))
    radixZ

carryBounds : Word64 → Set
carryBounds carry =
  zeroZ ≤Z unsignedZ carry
  ∧ unsignedZ carry ≤Z oneZ

trivialBounds : Set
trivialBounds =
  zeroZ ≤Z zeroZ
  ∧ zeroZ ≤Z oneZ

DivisionResult :
  (quotient remainderLow remainderHigh
   dl dh ul um uh : Word64) →
  Set
DivisionResult quotient remainderLow remainderHigh
  dl dh ul um uh =
  addInt
    (addInt
      (addInt
        (multiplyInt (unsignedZ quotient) (unsignedZ dl))
        (multiplyInt
          (multiplyInt radixZ (unsignedZ quotient))
          (unsignedZ dh)))
      (unsignedZ remainderLow))
    (multiplyInt radixZ (unsignedZ remainderHigh))
  ≡
  addInt
    (addInt
      (unsignedZ ul)
      (multiplyInt radixZ (unsignedZ um)))
    (multiplyInt
      (multiplyInt radixZ radixZ)
      (unsignedZ uh))
  ∧ zeroZ ≤Z
      addInt
        (unsignedZ remainderLow)
        (multiplyInt radixZ (unsignedZ remainderHigh))
  ∧ addInt
      (unsignedZ remainderLow)
      (multiplyInt radixZ (unsignedZ remainderHigh))
    <Z
    addInt
      (unsignedZ dl)
      (multiplyInt radixZ (unsignedZ dh))

FirstQuotientAfterIncrement :
  (dl dh ul um uh o3 bl1 bh1 : Word64) →
  Set
FirstQuotientAfterIncrement dl dh ul um uh o3 bl1 bh1 =
  (o5 : Word64) →
  unsignedZ o5 ≡
    euclideanModuloPositive
      (addInt (unsignedZ o3) oneZ)
      radixNat →
  DivisionResult o5 bl1 bh1 dl dh ul um uh

FirstHighSubtraction :
  (dl dh ul um uh o3 rh bl1 b1 : Word64) →
  Set
FirstHighSubtraction dl dh ul um uh o3 rh bl1 b1 =
  (bh1 b′1 : Word64) →
  (subtractInt
    (unsignedZ bh1)
    (multiplyInt radixZ (unsignedZ b′1))
   ≡
   subtractInt
    (subtractInt (unsignedZ rh) (unsignedZ dh))
    (unsignedZ b1)
   ∧ carryBounds b′1) →
  FirstQuotientAfterIncrement dl dh ul um uh o3 bl1 bh1

FirstLowSubtraction :
  (dl dh ul um uh o3 rl rh : Word64) →
  Set
FirstLowSubtraction dl dh ul um uh o3 rl rh =
  (bl1 b1 : Word64) →
  (subtractInt
    (unsignedZ bl1)
    (multiplyInt radixZ (unsignedZ b1))
   ≡
   subtractInt
    (subtractInt (unsignedZ rl) (unsignedZ dl))
    zeroZ
   ∧ carryBounds b1) →
  carryBounds b1
  ∧ FirstHighSubtraction dl dh ul um uh o3 rh bl1 b1

FirstFlagPremise :
  (dh dl rh rl : Word64) →
  (decision : Bool) →
  Set
FirstFlagPremise dh dl rh rl decision =
  IfSet
    (intLess (unsignedZ dh) (unsignedZ rh))
    (decision ≡ true)
    (Exists
      Bool
      (λ equalFlag →
        ((unsignedZ rh ≡ unsignedZ dh → equalFlag ≡ true)
         ∧ (equalFlag ≡ true → rh ≡ dh))
        ∧ decision ≡
          IfBool
            equalFlag
            (IfBool
              (intLessOrEqual (unsignedZ dl) (unsignedZ rl))
              true
              false)
            false))

FirstFlagObligation :
  (dl dh ul um uh o3 rl rh : Word64) →
  Set
FirstFlagObligation dl dh ul um uh o3 rl rh =
  (decision : Bool) →
  FirstFlagPremise dh dl rh rl decision →
  IfSet
    decision
    (trivialBounds
     ∧ FirstLowSubtraction dl dh ul um uh o3 rl rh)
    (DivisionResult o3 rl rh dl dh ul um uh)

FirstHighAddition :
  (dl dh ul um uh o3 bh rl c1 : Word64) →
  Set
FirstHighAddition dl dh ul um uh o3 bh rl c1 =
  (rh c′1 : Word64) →
  (addInt
    (unsignedZ rh)
    (multiplyInt radixZ (unsignedZ c′1))
   ≡
   addInt
    (addInt (unsignedZ bh) (unsignedZ dh))
    (unsignedZ c1)
   ∧ carryBounds c′1) →
  FirstFlagObligation dl dh ul um uh o3 rl rh

FirstLowAddition :
  (dl dh ul um uh o3 bl bh : Word64) →
  Set
FirstLowAddition dl dh ul um uh o3 bl bh =
  (rl c1 : Word64) →
  (addInt
    (unsignedZ rl)
    (multiplyInt radixZ (unsignedZ c1))
   ≡
   addInt
    (addInt (unsignedZ bl) (unsignedZ dl))
    zeroZ
   ∧ carryBounds c1) →
  carryBounds c1
  ∧ FirstHighAddition dl dh ul um uh o3 bh rl c1

FirstCorrection :
  (dl dh ul um uh o1 bl bh : Word64) →
  Set
FirstCorrection dl dh ul um uh o1 bl bh =
  (o3 : Word64) →
  unsignedZ o3 ≡
    euclideanModuloPositive
      (subtractInt (unsignedZ o1) oneZ)
      radixNat →
  trivialBounds
  ∧ FirstLowAddition dl dh ul um uh o3 bl bh

SecondQuotientAfterIncrement :
  (dl dh ul um uh o1 bl1 bh1 : Word64) →
  Set
SecondQuotientAfterIncrement dl dh ul um uh o1 bl1 bh1 =
  (o4 : Word64) →
  unsignedZ o4 ≡
    euclideanModuloPositive
      (addInt (unsignedZ o1) oneZ)
      radixNat →
  DivisionResult o4 bl1 bh1 dl dh ul um uh

SecondHighSubtraction :
  (dl dh ul um uh o1 bh bl1 b3 : Word64) →
  Set
SecondHighSubtraction dl dh ul um uh o1 bh bl1 b3 =
  (bh1 b′1 : Word64) →
  (subtractInt
    (unsignedZ bh1)
    (multiplyInt radixZ (unsignedZ b′1))
   ≡
   subtractInt
    (subtractInt (unsignedZ bh) (unsignedZ dh))
    (unsignedZ b3)
   ∧ carryBounds b′1) →
  SecondQuotientAfterIncrement dl dh ul um uh o1 bl1 bh1

SecondLowSubtraction :
  (dl dh ul um uh o1 bl bh : Word64) →
  Set
SecondLowSubtraction dl dh ul um uh o1 bl bh =
  (bl1 b3 : Word64) →
  (subtractInt
    (unsignedZ bl1)
    (multiplyInt radixZ (unsignedZ b3))
   ≡
   subtractInt
    (subtractInt (unsignedZ bl) (unsignedZ dl))
    zeroZ
   ∧ carryBounds b3) →
  carryBounds b3
  ∧ SecondHighSubtraction dl dh ul um uh o1 bh bl1 b3

SecondFlagPremise :
  (dh dl bh bl : Word64) →
  (decision : Bool) →
  Set
SecondFlagPremise dh dl bh bl decision =
  IfSet
    (intLess (unsignedZ dh) (unsignedZ bh))
    (decision ≡ true)
    (Exists
      Bool
      (λ equalFlag →
        ((unsignedZ bh ≡ unsignedZ dh → equalFlag ≡ true)
         ∧ (equalFlag ≡ true → bh ≡ dh))
        ∧ decision ≡
          IfBool
            equalFlag
            (IfBool
              (intLessOrEqual (unsignedZ dl) (unsignedZ bl))
              true
              false)
            false))

SecondFlagObligation :
  (dl dh ul um uh o1 bl bh : Word64) →
  Set
SecondFlagObligation dl dh ul um uh o1 bl bh =
  (decision : Bool) →
  SecondFlagPremise dh dl bh bl decision →
  IfSet
    decision
    (trivialBounds
     ∧ SecondLowSubtraction dl dh ul um uh o1 bl bh)
    (DivisionResult o1 bl bh dl dh ul um uh)

CorrectionBranches :
  (dl dh ul um uh sl o1 bl bh : Word64) →
  Set
CorrectionBranches dl dh ul um uh sl o1 bl bh =
  IfSet
    (intLessOrEqual (unsignedZ sl) (unsignedZ bh))
    (FirstCorrection dl dh ul um uh o1 bl bh)
    (SecondFlagObligation dl dh ul um uh o1 bl bh)

AfterSecondHighBorrow :
  (dl dh ul um uh sl o1 ih bl b2 : Word64) →
  Set
AfterSecondHighBorrow dl dh ul um uh sl o1 ih bl b2 =
  (bh b2′ : Word64) →
  (subtractInt
    (unsignedZ bh)
    (multiplyInt radixZ (unsignedZ b2′))
   ≡
   subtractInt
    (subtractInt (unsignedZ ih) (unsignedZ dh))
    (unsignedZ b2)
   ∧ carryBounds b2′) →
  CorrectionBranches dl dh ul um uh sl o1 bl bh

AfterSecondLowBorrow :
  (dl dh ul um uh sl o1 il ih : Word64) →
  Set
AfterSecondLowBorrow dl dh ul um uh sl o1 il ih =
  (bl b2 : Word64) →
  (subtractInt
    (unsignedZ bl)
    (multiplyInt radixZ (unsignedZ b2))
   ≡
   subtractInt
    (subtractInt (unsignedZ il) (unsignedZ dl))
    zeroZ
   ∧ carryBounds b2) →
  carryBounds b2
  ∧ AfterSecondHighBorrow dl dh ul um uh sl o1 ih bl b2

AfterFirstHighBorrow :
  (dl dh ul um uh sl o1 o2 th il b : Word64) →
  Set
AfterFirstHighBorrow dl dh ul um uh sl o1 o2 th il b =
  (ih b′ : Word64) →
  (subtractInt
    (unsignedZ ih)
    (multiplyInt radixZ (unsignedZ b′))
   ≡
   subtractInt
    (subtractInt (unsignedZ o2) (unsignedZ th))
    (unsignedZ b)
   ∧ carryBounds b′) →
  trivialBounds
  ∧ AfterSecondLowBorrow dl dh ul um uh sl o1 il ih

AfterFirstLowBorrow :
  (dl dh ul um uh sl o1 o2 tl th : Word64) →
  Set
AfterFirstLowBorrow dl dh ul um uh sl o1 o2 tl th =
  (il b : Word64) →
  (subtractInt
    (unsignedZ il)
    (multiplyInt radixZ (unsignedZ b))
   ≡
   subtractInt
    (subtractInt (unsignedZ ul) (unsignedZ tl))
    zeroZ
   ∧ carryBounds b) →
  carryBounds b
  ∧ AfterFirstHighBorrow dl dh ul um uh sl o1 o2 th il b

AfterLowProduct :
  (dl dh ul um uh sl sh o1 o2 : Word64) →
  Set
AfterLowProduct dl dh ul um uh sl sh o1 o2 =
  (tl th : Word64) →
  addInt
    (unsignedZ tl)
    (multiplyInt radixZ (unsignedZ th))
  ≡ multiplyInt (unsignedZ sh) (unsignedZ dl) →
  trivialBounds
  ∧ AfterFirstLowBorrow dl dh ul um uh sl o1 o2 tl th

AfterO2 :
  (dl dh ul um uh sl sh o1 p : Word64) →
  Set
AfterO2 dl dh ul um uh sl sh o1 p =
  (o2 : Word64) →
  unsignedZ o2 ≡
    euclideanModuloPositive
      (subtractInt (unsignedZ um) (unsignedZ p))
      radixNat →
  Not (addInt max64Z oneZ ≡ zeroZ)
  ∧ AfterLowProduct dl dh ul um uh sl sh o1 o2

AfterP :
  (dl dh ul um uh sl sh o1 : Word64) →
  Set
AfterP dl dh ul um uh sl sh o1 =
  (p : Word64) →
  unsignedZ p ≡
    euclideanModuloPositive
      (multiplyInt (unsignedZ dh) (unsignedZ sh))
      radixNat →
  AfterO2 dl dh ul um uh sl sh o1 p

AfterO1 :
  (dl dh ul um uh sl sh : Word64) →
  Set
AfterO1 dl dh ul um uh sl sh =
  (o1 : Word64) →
  unsignedZ o1 ≡
    euclideanModuloPositive
      (addInt (unsignedZ sh) oneZ)
      radixNat →
  AfterP dl dh ul um uh sl sh o1

HighAddObligation :
  (dl dh ul um uh h sl c : Word64) →
  Set
HighAddObligation dl dh ul um uh h sl c =
  (sh c′ : Word64) →
  (addInt
    (unsignedZ sh)
    (multiplyInt radixZ (unsignedZ c′))
   ≡
   addInt
    (addInt (unsignedZ uh) (unsignedZ h))
    (unsignedZ c)
   ∧ carryBounds c′) →
  AfterO1 dl dh ul um uh sl sh

LowAddObligation :
  (dl dh ul um uh l h : Word64) →
  Set
LowAddObligation dl dh ul um uh l h =
  (sl c : Word64) →
  (addInt
    (unsignedZ sl)
    (multiplyInt radixZ (unsignedZ c))
   ≡
   addInt
    (addInt (unsignedZ um) (unsignedZ l))
    zeroZ
   ∧ carryBounds c) →
  carryBounds c
  ∧ HighAddObligation dl dh ul um uh h sl c

div3by2-inv'vc : Set
div3by2-inv'vc =
  (dh v dl um uh l h ul : Word64) →
  halfRadixZ ≤Z unsignedZ dh →
  reciprocal3by2 v dh dl →
  addInt
    (unsignedZ um)
    (multiplyInt radixZ (unsignedZ uh))
  <Z
  addInt
    (unsignedZ dl)
    (multiplyInt radixZ (unsignedZ dh)) →
  addInt
    (unsignedZ l)
    (multiplyInt radixZ (unsignedZ h))
  ≡
  multiplyInt (unsignedZ v) (unsignedZ uh) →
  zeroZ ≤Z zeroZ
  ∧ zeroZ ≤Z oneZ
  ∧ LowAddObligation dl dh ul um uh l h
