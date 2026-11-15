-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/multiprecision/sub_Sub_sub_rxqtvc: the verification condition for
-- alias-aware unequal-length multiprecision subtraction into the first
-- operand, including borrow, memory framing, validity, and preservation of
-- the second operand and pointer metadata. This file contains no proof.

{-# OPTIONS --safe #-}

module sub_Sub_sub_rxqtvc where

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

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

powerNat : Int → Nat → Int
powerNat base zero = oneZ
powerNat base (suc exponent) =
  multiplyInt base (powerNat base exponent)

powerInt : Int → Int → Int
powerInt base exponent = powerNat base (toNat exponent)

data Vec (A : Set) : Nat → Set where
  []V  : Vec A zero
  _∷V_ : {n : Nat} → A → Vec A n → Vec A (suc n)

bitValue : Bool → Nat
bitValue false = zero
bitValue true = suc zero

unsignedNat : {n : Nat} → Vec Bool n → Nat
unsignedNat []V = zero
unsignedNat (bit ∷V bits) =
  bitValue bit + 2 * unsignedNat bits

Word32 Word64 : Set
Word32 = Vec Bool 32
Word64 = Vec Bool 64

signed32 : Word32 → Int
signed32 word with natLess (unsignedNat word) 2147483648
... | true = pos (unsignedNat word)
... | false = difference (unsignedNat word) 4294967296

unsigned64 : Word64 → Int
unsigned64 word = pos (unsignedNat word)

minInt32 maxInt32 radix : Int
minInt32 = negsuc 2147483647
maxInt32 = pos 2147483647
radix = pos 18446744073709551616

module MultiprecisionTheory
  (Zone : Set)
  (zoneWitness : Zone)
  where

  record Array64 : Set where
    constructor array
    field
      arrayLength : Nat
      arrayElts   : Int → Word64

  open Array64

  record Ptr : Set where
    constructor ptr
    field
      ptrData     : Array64
      ptrOffset   : Int
      ptrMin      : Int
      ptrMax      : Int
      ptrWritable : Bool
      ptrZone     : Zone

  open Ptr

  record Mem : Set where
    constructor mem
    field
      memZr : Zone
      memZx : Zone
      memZy : Zone
      memMr : Word32
      memMx : Word32
      memMy : Word32
      memLr : Word32
      memLx : Word32
      memLy : Word32
      memOk : Bool

  open Mem

  plength : Ptr → Int
  plength pointer = pos (arrayLength (ptrData pointer))

  pelts : Ptr → Int → Word64
  pelts pointer = arrayElts (ptrData pointer)

  ArrayEqual : Array64 → Array64 → Set
  ArrayEqual leftArray rightArray =
    arrayLength leftArray ≡ arrayLength rightArray
    ∧
    ((index : Int) →
      arrayElts leftArray index ≡ arrayElts rightArray index)

  EverywhereEqual : Ptr → Ptr → Set
  EverywhereEqual leftPointer rightPointer =
    (index : Int) →
    pelts leftPointer index ≡ pelts rightPointer index

  int32InBounds : Int → Set
  int32InBounds value =
    minInt32 ≤Z value ∧ value ≤Z maxInt32

  Valid : Ptr → Int → Set
  Valid pointer size =
    int32InBounds size
    ∧ zeroZ ≤Z size
    ∧ zeroZ ≤Z ptrMin pointer
    ∧ ptrMin pointer ≤Z ptrOffset pointer
    ∧ addInt (ptrOffset pointer) size ≤Z ptrMax pointer
    ∧ ptrMax pointer ≤Z plength pointer

  valueFrom : (Int → Word64) → Int → Nat → Int
  valueFrom elements index zero = zeroZ
  valueFrom elements index (suc count) =
    addInt
      (unsigned64 (elements index))
      (multiplyInt
        radix
        (valueFrom elements (addInt index oneZ) count))

  value : Ptr → Int → Int
  value pointer size =
    valueFrom
      (pelts pointer)
      (ptrOffset pointer)
      (toNat size)

  MapEqSub : Ptr → Ptr → Int → Int → Set
  MapEqSub current old lower upper =
    (index : Int) →
    (lower ≤Z index ∧ index <Z upper) →
    pelts current index ≡ pelts old index

  MapEqSubShift :
    Ptr →
    Ptr →
    Int →
    Int →
    Int →
    Set
  MapEqSubShift current old currentOffset oldOffset size =
    (index : Int) →
    (zeroZ ≤Z index ∧ index <Z size) →
    pelts current (addInt currentOffset index)
      ≡ pelts old (addInt oldOffset index)

  OutsideEqual : Ptr → Ptr → Int → Int → Set
  OutsideEqual current old start size =
    (index : Int) →
    (index <Z start ∨ addInt start size ≤Z index) →
    pelts current index ≡ pelts old index

  Identical : Ptr → Ptr → Set
  Identical leftPointer rightPointer =
    ArrayEqual (ptrData leftPointer) (ptrData rightPointer)
    ∧ ptrOffset leftPointer ≡ ptrOffset rightPointer
    ∧ ptrMin leftPointer ≡ ptrMin rightPointer
    ∧ ptrMax leftPointer ≡ ptrMax rightPointer
    ∧ ptrZone leftPointer ≡ ptrZone rightPointer

  View : Ptr → Ptr → Set
  View current old =
    ptrOffset current ≡ ptrOffset old
    ∧ ptrWritable current ≡ ptrWritable old
    ∧ ptrZone current ≡ ptrZone old

  ViewWithMin : Ptr → Ptr → Set
  ViewWithMin current old =
    ptrOffset current ≡ ptrOffset old
    ∧ ptrMin current ≡ ptrMin old
    ∧ ptrWritable current ≡ ptrWritable old
    ∧ ptrZone current ≡ ptrZone old

  FullView : Ptr → Ptr → Set
  FullView current old =
    ptrOffset current ≡ ptrOffset old
    ∧ ptrMin current ≡ ptrMin old
    ∧ ptrMax current ≡ ptrMax old
    ∧ ptrWritable current ≡ ptrWritable old
    ∧ ptrZone current ≡ ptrZone old

  MemView : Mem → Mem → Set
  MemView current old =
    memZr current ≡ memZr old
    ∧ memZx current ≡ memZx old
    ∧ memZy current ≡ memZy old
    ∧ memMr current ≡ memMr old
    ∧ memMx current ≡ memMx old
    ∧ memMy current ≡ memMy old
    ∧ memLr current ≡ memLr old
    ∧ memLx current ≡ memLx old
    ∧ memLy current ≡ memLy old

  DisjointOrEqual :
    Ptr →
    Ptr →
    Int →
    Int →
    Set
  DisjointOrEqual result operand resultSize operandSize =
    ptrOffset result ≡ ptrOffset operand
    ∨ addInt (ptrOffset result) resultSize ≤Z ptrOffset operand
    ∨ addInt (ptrOffset operand) operandSize ≤Z ptrOffset result

  Separated :
    Ptr →
    Ptr →
    Int →
    Int →
    Set
  Separated leftPointer rightPointer leftSize rightSize =
    (zeroZ ≤Z ptrOffset leftPointer
     ∧
     addInt (ptrOffset leftPointer) leftSize
       ≤Z ptrOffset rightPointer)
    ∨
    (zeroZ ≤Z ptrOffset rightPointer
     ∧
     addInt (ptrOffset rightPointer) rightSize
       ≤Z ptrOffset leftPointer)

  ReboundView : Ptr → Ptr → Ptr → Set
  ReboundView current sharedData old =
    ArrayEqual (ptrData current) (ptrData sharedData)
    ∧ plength sharedData ≡ plength old
    ∧ FullView current old

  ReboundResultView : Ptr → Ptr → Set
  ReboundResultView current old =
    plength current ≡ plength old
    ∧ FullView current old

  FinalPostcondition :
    Word32 →
    Word32 →
    Ptr →
    Ptr →
    Ptr →
    Ptr →
    Word64 →
    Set
  FinalPostcondition sxWord syWord x y x2 y2 result =
    let sx = signed32 sxWord
        sy = signed32 syWord
    in
    subtractInt
      (value x2 sx)
      (multiplyInt (powerInt radix sx) (unsigned64 result))
      ≡ subtractInt (value x sx) (value y sy)
    ∧ zeroZ ≤Z unsigned64 result
    ∧ unsigned64 result ≤Z oneZ
    ∧ OutsideEqual x2 x (ptrOffset x2) sx
    ∧ EverywhereEqual y2 y
    ∧ value y2 sy ≡ value y sy
    ∧ ptrMin x2 ≡ ptrMin x
    ∧ ptrMax x2 ≡ ptrMax x
    ∧ plength x2 ≡ plength x
    ∧ ptrMin y2 ≡ ptrMin y
    ∧ ptrMax y2 ≡ ptrMax y
    ∧ plength y2 ≡ plength y

  CloseContinuation :
    Word32 →
    Word32 →
    Ptr →
    Ptr →
    Ptr →
    Ptr →
    Word64 →
    Mem →
    Ptr →
    Ptr →
    Set
  CloseContinuation
    sxWord syWord x y x1 y1 result memory nx1 ny1 =
    (memory1 : Mem) →
    (ny2 nx2 y2 x2 : Ptr) →
    MemView memory1 memory →
    View ny2 ny1 →
    View nx2 nx1 →
    ViewWithMin y2 y1 →
    ViewWithMin x2 x1 →
    let sx = signed32 sxWord
        sy = signed32 syWord
    in
    (ptrMax x2 ≡ signed32 (memMx memory1)
     ∧ ptrMax y2 ≡ signed32 (memMy memory1)
     ∧ MapEqSubShift
         nx1 x2 (ptrOffset nx2) (ptrOffset x2) sx
     ∧ MapEqSubShift
         ny1 y2 (ptrOffset ny2) (ptrOffset y2) sy
     ∧ OutsideEqual x2 x1 (ptrOffset x2) sx
     ∧ OutsideEqual y2 y1 (ptrOffset y2) sy
     ∧ plength x2 ≡ plength x1
     ∧ plength y2 ≡ plength y1
     ∧ ptrMin x2 ≡ ptrMin x1
     ∧ ptrMin y2 ≡ ptrMin y1)
    →
    FinalPostcondition sxWord syWord x y x2 y2 result

  ResultHypothesis :
    Word32 →
    Word32 →
    Ptr →
    Ptr →
    Ptr →
    Ptr →
    Ptr →
    Ptr →
    Word64 →
    Set
  ResultHypothesis
    sxWord syWord nr1 nr nx1 nx ny1 ny result =
    let sx = signed32 sxWord
        sy = signed32 syWord
    in
    subtractInt
      (value nr1 sx)
      (multiplyInt (powerInt radix sx) (unsigned64 result))
      ≡ subtractInt (value nx sx) (value ny sy)
    ∧ zeroZ ≤Z unsigned64 result
    ∧ unsigned64 result ≤Z oneZ
    ∧ OutsideEqual nr1 nr (ptrOffset nr1) sx
    ∧
    (ptrOffset nr1 ≡ ptrOffset nx1
     ∨
     MapEqSub
       nx1 nx
       (ptrOffset nx1)
       (addInt (ptrOffset nx1) sx))
    ∧
    (ptrOffset nr1 ≡ ptrOffset ny1
     ∨
     MapEqSub
       ny1 ny
       (ptrOffset ny1)
       (addInt (ptrOffset ny1) sy))

  Preclose :
    Word32 →
    Word32 →
    Ptr →
    Ptr →
    Ptr →
    Ptr →
    Ptr →
    Mem →
    Set
  Preclose sxWord syWord x1 y1 nr1 nx1 ny1 memory =
    let sx = signed32 sxWord
        sy = signed32 syWord
    in
    ptrWritable x1 ≡ true
    ∧ ptrWritable nr1 ≡ true
    ∧ memOk memory ≡ true
    ∧ zeroZ ≤Z sy
    ∧ sy ≤Z sx
    ∧ Identical nr1 nx1
    ∧ Separated nx1 ny1 sx sy
    ∧ memZx memory ≡ ptrZone x1
    ∧ memZy memory ≡ ptrZone y1
    ∧ memLx memory ≡ sxWord
    ∧ memLy memory ≡ syWord

  ResultContinuation :
    Word32 →
    Word32 →
    Ptr →
    Ptr →
    Ptr →
    Ptr →
    Ptr →
    Ptr →
    Ptr →
    Mem →
    Ptr →
    Ptr →
    Ptr →
    Set
  ResultContinuation
    sxWord syWord x y x1 y1 nr nx ny memory nx1 ny1 nr1 =
    (result : Word64) →
    ResultHypothesis
      sxWord syWord nr1 nr nx1 nx ny1 ny result
    →
    Preclose sxWord syWord x1 y1 nr1 nx1 ny1 memory
    ∧ CloseContinuation
        sxWord syWord x y x1 y1 result memory nx1 ny1

  ReboundContinuation :
    Word32 →
    Word32 →
    Ptr →
    Ptr →
    Ptr →
    Ptr →
    Ptr →
    Ptr →
    Ptr →
    Mem →
    Set
  ReboundContinuation
    sxWord syWord x y x1 y1 nr nx ny memory =
    (ny1 nx1 nr1 : Ptr) →
    ReboundView ny1 nr1 ny →
    ReboundView nx1 nr1 nx →
    ReboundResultView nr1 nr →
    ResultContinuation
      sxWord syWord x y x1 y1 nr nx ny memory nx1 ny1 nr1

  OpenHypothesis :
    Word32 →
    Word32 →
    Ptr →
    Ptr →
    Ptr →
    Ptr →
    Ptr →
    Ptr →
    Ptr →
    Mem →
    Set
  OpenHypothesis sxWord syWord x y x1 y1 nr nx ny memory =
    let sx = signed32 sxWord
        sy = signed32 syWord
    in
    ptrWritable nr ≡ true
    ∧ value nx sx ≡ value x sx
    ∧ value ny sy ≡ value y sy
    ∧ Valid nx sx
    ∧ Valid ny sy
    ∧ Identical nr nx
    ∧ Separated nx ny sx sy
    ∧ memZx memory ≡ ptrZone x1
    ∧ memZy memory ≡ ptrZone y1
    ∧ signed32 (memMx memory) ≡ ptrMax x
    ∧ signed32 (memMy memory) ≡ ptrMax y
    ∧ memLx memory ≡ sxWord
    ∧ memLy memory ≡ syWord
    ∧ memOk memory ≡ true
    ∧ MapEqSubShift
        nx x1 (ptrOffset nx) (ptrOffset x1) sx
    ∧ MapEqSubShift
        ny y1 (ptrOffset ny) (ptrOffset y1) sy
    ∧ EverywhereEqual x1 x
    ∧ EverywhereEqual y1 y
    ∧ plength x1 ≡ plength x
    ∧ plength y1 ≡ plength y
    ∧ ptrMin x1 ≡ ptrMin x
    ∧ ptrMin y1 ≡ ptrMin y
    ∧ ArrayEqual (ptrData nr) (ptrData nx)
    ∧ ArrayEqual (ptrData nx) (ptrData ny)

  OpenConclusion :
    Word32 →
    Word32 →
    Ptr →
    Ptr →
    Ptr →
    Set
  OpenConclusion sxWord syWord nr nx ny =
    let sx = signed32 sxWord
        sy = signed32 syWord
    in
    zeroZ ≤Z sy
    ∧ sy ≤Z sx
    ∧ Valid nr sx
    ∧ Valid nx sx
    ∧ Valid ny sy
    ∧ DisjointOrEqual nr nx sx sx
    ∧ DisjointOrEqual nr ny sx sy
    ∧ ArrayEqual (ptrData nr) (ptrData nx)
    ∧ ArrayEqual (ptrData nx) (ptrData ny)
    ∧ ptrWritable nr ≡ true

  OpenContinuation :
    Word32 →
    Word32 →
    Ptr →
    Ptr →
    Ptr →
    Ptr →
    Set
  OpenContinuation sxWord syWord x y x1 y1 =
    (nr nx ny : Ptr) →
    (memory : Mem) →
    OpenHypothesis sxWord syWord x y x1 y1 nr nx ny memory
    →
    OpenConclusion sxWord syWord nr nx ny
    ∧ ReboundContinuation
        sxWord syWord x y x1 y1 nr nx ny memory

  ViewContinuation :
    Word32 →
    Word32 →
    Ptr →
    Ptr →
    Set
  ViewContinuation sxWord syWord x y =
    (y1 x1 : Ptr) →
    View y1 y →
    View x1 x →
    OpenContinuation sxWord syWord x y x1 y1

  SubRxVC : Word32 → Word32 → Ptr → Ptr → Set
  SubRxVC syWord sxWord x y =
    zeroZ ≤Z signed32 syWord →
    signed32 syWord ≤Z signed32 sxWord →
    Valid x (signed32 sxWord) →
    Valid y (signed32 syWord) →
    ptrWritable x ≡ true →
    Valid x (signed32 sxWord)
    ∧ Valid y (signed32 syWord)
    ∧ zeroZ ≤Z signed32 syWord
    ∧ signed32 syWord ≤Z signed32 sxWord
    ∧ ptrWritable x ≡ true
    ∧ ViewContinuation sxWord syWord x y

  sub-rx-vc : Set
  sub-rx-vc =
    (syWord sxWord : Word32) →
    (x y : Ptr) →
    SubRxVC syWord sxWord x y
