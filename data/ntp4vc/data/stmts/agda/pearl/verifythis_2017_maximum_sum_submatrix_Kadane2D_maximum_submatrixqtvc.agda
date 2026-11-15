-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2017_maximum_sum_submatrix_Kadane2D_maximum_submatrixqtvc:
-- the verification condition for Kadane's two-dimensional maximum-sum
-- submatrix algorithm, including its nested-loop invariants. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module MaximumSumSubmatrixKadane2DMaximumSubmatrixQtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
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

differenceNat : Nat → Nat → Int
differenceNat zero zero = pos zero
differenceNat (suc m) zero = pos (suc m)
differenceNat zero (suc n) = negsuc n
differenceNat (suc m) (suc n) = differenceNat m n

addInt : Int → Int → Int
addInt (pos m) (pos n) = pos (m + n)
addInt (pos m) (negsuc n) = differenceNat m (suc n)
addInt (negsuc m) (pos n) = differenceNat n (suc m)
addInt (negsuc m) (negsuc n) = negsuc (suc (m + n))

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

natToInt : Nat → Int
natToInt = pos

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = natToInt (length xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) = nthDefault default n xs

nthInt : List Int → Int → Int
nthInt xs index = nthDefault zeroZ (toNat index) xs

updateList : {A : Set} → List A → Nat → A → List A
updateList [] index value = []
updateList (x ∷ xs) zero value = value ∷ xs
updateList (x ∷ xs) (suc index) value =
  x ∷ updateList xs index value

IfInt : Bool → Int → Int → Int
IfInt true when-true when-false = when-true
IfInt false when-true when-false = when-false

updateFunction :
  (Int → Int) →
  Int →
  Int →
  Int →
  Int
updateFunction old index value query =
  IfInt (intEqual query index) value (old query)

PointwiseEqual :
  {A B : Set} →
  (A → B) →
  (A → B) →
  Set
PointwiseEqual f g = (x : _) → f x ≡ g x

ArrayPointwiseEqual :
  List Int →
  (Int → Int) →
  (Int → Int) →
  Set
ArrayPointwiseEqual entries f g =
  (index : Int) →
  (zeroZ ≤Z index ∧ index <Z lengthZ entries) →
  f index ≡ g index

sumCount : (Int → Int) → Int → Nat → Int
sumCount f lower zero = zeroZ
sumCount f lower (suc count) =
  addInt (f lower) (sumCount f (addInt lower oneZ) count)

sumRange : (Int → Int) → Int → Int → Int
sumRange f lower upper =
  sumCount f lower (toNat (subtractInt upper lower))

arraySum : List Int → Int → Int → Int
arraySum values lower upper =
  sumRange (nthInt values) lower upper

record Matrix : Set where
  constructor matrix
  field
    rowCount    : Nat
    columnCount : Nat
    matrixElts  : Int → Int → Int

open Matrix

rows : Matrix → Int
rows m = natToInt (rowCount m)

columns : Matrix → Int
columns m = natToInt (columnCount m)

elts : Matrix → Int → Int → Int
elts m row column = matrixElts m row column

validIndex : Matrix → Int → Int → Set
validIndex m row column =
  ((zeroZ ≤Z row) ∧ (row <Z rows m)) ∧
  ((zeroZ ≤Z column) ∧ (column <Z columns m))

col : Matrix → Int → Int → Int
col m column row = elts m row column

matrixSum : Matrix → Int → Int → Int → Int → Int
matrixSum m rowLow rowHigh columnLow columnHigh =
  sumRange
    (λ column → sumRange (col m column) rowLow rowHigh)
    columnLow
    columnHigh

RowBounds : Matrix → Int → Int → Set
RowBounds m rowLow rowHigh =
  (zeroZ ≤Z rowLow) ∧
  (rowLow ≤Z rowHigh) ∧
  (rowHigh ≤Z rows m)

ColumnBounds : Matrix → Int → Int → Set
ColumnBounds m columnLow columnHigh =
  (zeroZ ≤Z columnLow) ∧
  (columnLow ≤Z columnHigh) ∧
  (columnHigh ≤Z columns m)

RectangleBounds :
  Matrix →
  Int →
  Int →
  Int →
  Int →
  Set
RectangleBounds m rowLow rowHigh columnLow columnHigh =
  RowBounds m rowLow rowHigh ∧
  ColumnBounds m columnLow columnHigh

StateValue :
  Matrix →
  Int →
  Int →
  Int →
  Int →
  Int →
  Set
StateValue m rowLow rowHigh columnLow columnHigh maximum =
  maximum ≡ matrixSum m rowLow rowHigh columnLow columnHigh ∧
  zeroZ ≤Z matrixSum m rowLow rowHigh columnLow columnHigh

BestBeforeRow : Matrix → Int → Int → Set
BestBeforeRow m currentRow maximum =
  (rowLow rowHigh : Int) →
  ((zeroZ ≤Z rowLow) ∧ (rowLow <Z currentRow)) →
  ((rowLow ≤Z rowHigh) ∧ (rowHigh ≤Z rows m)) →
  (columnLow columnHigh : Int) →
  ColumnBounds m columnLow columnHigh →
  matrixSum m rowLow rowHigh columnLow columnHigh ≤Z maximum

BeforePair :
  Int →
  Int →
  Int →
  Int →
  Set
BeforePair currentRow currentHigh rowLow rowHigh =
  (rowLow <Z currentRow) ∨
  ((rowLow ≡ currentRow) ∧ (rowHigh <Z currentHigh))

BestBeforePair :
  Matrix →
  Int →
  Int →
  Int →
  Set
BestBeforePair m currentRow currentHigh maximum =
  (rowLow rowHigh : Int) →
  RowBounds m rowLow rowHigh →
  BeforePair currentRow currentHigh rowLow rowHigh →
  (columnLow columnHigh : Int) →
  ColumnBounds m columnLow columnHigh →
  matrixSum m rowLow rowHigh columnLow columnHigh ≤Z maximum

ColumnSumsBeforeHigh :
  Matrix →
  Int →
  Int →
  List Int →
  Set
ColumnSumsBeforeHigh m rowLow rowHigh values =
  (column : Int) →
  ((zeroZ ≤Z column) ∧ (column <Z columns m)) →
  nthInt values column ≡
    sumRange
      (col m column)
      rowLow
      (subtractInt rowHigh oneZ)

OuterState :
  Matrix →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Set
OuterState
  m currentRow rowLow rowHigh columnLow columnHigh maximum =
  RectangleBounds m rowLow rowHigh columnLow columnHigh ∧
  StateValue m rowLow rowHigh columnLow columnHigh maximum ∧
  BestBeforeRow m currentRow maximum

InnerState :
  Matrix →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  List Int →
  Set
InnerState
  m currentRow currentHigh
  rowLow rowHigh columnLow columnHigh maximum values =
  RectangleBounds m rowLow rowHigh columnLow columnHigh ∧
  StateValue m rowLow rowHigh columnLow columnHigh maximum ∧
  BestBeforePair m currentRow currentHigh maximum ∧
  ColumnSumsBeforeHigh m currentRow currentHigh values

FinalPostcondition :
  Matrix →
  Int →
  Int →
  Int →
  Int →
  Int →
  Set
FinalPostcondition m maximum rowLow rowHigh columnLow columnHigh =
  RectangleBounds m rowLow rowHigh columnLow columnHigh ∧
  maximum ≡ matrixSum m rowLow rowHigh columnLow columnHigh ∧
  ((otherRowLow otherRowHigh : Int) →
   RowBounds m otherRowLow otherRowHigh →
   (otherColumnLow otherColumnHigh : Int) →
   ColumnBounds m otherColumnLow otherColumnHigh →
   matrixSum
     m
     otherRowLow
     otherRowHigh
     otherColumnLow
     otherColumnHigh
     ≤Z maximum)

SubarrayMaximum :
  List Int →
  Int →
  Int →
  Set
SubarrayMaximum values low high =
  ((zeroZ ≤Z low) ∧
   (low ≤Z high) ∧
   (high ≤Z lengthZ values)) ∧
  ((otherLow otherHigh : Int) →
   ((zeroZ ≤Z otherLow) ∧
    (otherLow ≤Z otherHigh) ∧
    (otherHigh ≤Z lengthZ values)) →
   arraySum values otherLow otherHigh
     ≤Z arraySum values low high)

MaximumSubarrayStep :
  Matrix →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  List Int →
  Set
MaximumSubarrayStep
  m currentRow currentHigh
  rowLow rowHigh columnLow columnHigh maximum values =
  (low high : Int) →
  SubarrayMaximum values low high →
  IfSet
    (intLess maximum (arraySum values low high))
    (InnerState
      m
      currentRow
      (addInt currentHigh oneZ)
      currentRow
      currentHigh
      low
      high
      (arraySum values low high)
      values)
    (InnerState
      m
      currentRow
      (addInt currentHigh oneZ)
      rowLow
      rowHigh
      columnLow
      columnHigh
      maximum
      values)

ProcessedColumns :
  Matrix →
  Int →
  Int →
  List Int →
  Int →
  Set
ProcessedColumns m rowLow rowHigh values split =
  (column : Int) →
  ((zeroZ ≤Z column) ∧ (column <Z split)) →
  nthInt values column ≡
    sumRange (col m column) rowLow rowHigh

UnprocessedColumns :
  Matrix →
  Int →
  Int →
  List Int →
  Int →
  Set
UnprocessedColumns m rowLow rowHigh values split =
  (column : Int) →
  ((split ≤Z column) ∧ (column <Z columns m)) →
  nthInt values column ≡
    sumRange
      (col m column)
      rowLow
      (subtractInt rowHigh oneZ)

ColumnInvariant :
  Matrix →
  Int →
  Int →
  List Int →
  Int →
  Set
ColumnInvariant m rowLow rowHigh values split =
  ProcessedColumns m rowLow rowHigh values split ∧
  UnprocessedColumns m rowLow rowHigh values split

UpdateObligation :
  Matrix →
  Int →
  Int →
  List Int →
  Int →
  Set
UpdateObligation m rowLow rowHigh values column =
  let previousRow = subtractInt rowHigh oneZ
      newValue =
        addInt
          (nthInt values column)
          (elts m previousRow column)
      updated = updateList values (toNat column) newValue
  in
  validIndex m previousRow column ∧
  ((zeroZ ≤Z column) ∧ (column <Z lengthZ values)) ∧
  ((zeroZ ≤Z column) ∧ (column <Z lengthZ values)) ∧
  (length updated ≡ length values →
  ArrayPointwiseEqual updated
    (nthInt updated)
    (updateFunction (nthInt values) column newValue) →
   ColumnInvariant
     m
     rowLow
     rowHigh
     updated
     (addInt column oneZ))

ColumnLoopVC :
  Matrix →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  List Int →
  Set
ColumnLoopVC
  m currentRow currentHigh
  stateRowLow stateRowHigh stateColumnLow stateColumnHigh maximum values =
  let upper = subtractInt (columns m) oneZ
  in
  (zeroZ ≤Z addInt upper oneZ →
   (ProcessedColumns m currentRow currentHigh values zeroZ ∧
    UnprocessedColumns m currentRow currentHigh values zeroZ) ∧
   ((current : List Int) →
    length current ≡ length values →
    (((column : Int) →
      (((zeroZ ≤Z column) ∧ (column ≤Z upper)) ∧
       ColumnInvariant m currentRow currentHigh current column) →
      UpdateObligation m currentRow currentHigh current column) ∧
     (ColumnInvariant
        m
        currentRow
        currentHigh
        current
        (addInt upper oneZ) →
      MaximumSubarrayStep
        m
        currentRow
        currentHigh
        stateRowLow
        stateRowHigh
        stateColumnLow
        stateColumnHigh
        maximum
        current)))) ∧
  (addInt upper oneZ <Z zeroZ →
   MaximumSubarrayStep
     m
     currentRow
     currentHigh
     stateRowLow
     stateRowHigh
     stateColumnLow
     stateColumnHigh
     maximum
     values)

InnerIterationObligations :
  Matrix →
  Int →
  Int →
  List Int →
  Set
InnerIterationObligations m currentRow firstHigh initialValues =
  (stateColumnHigh stateColumnLow stateRowHigh stateRowLow maximum : Int) →
  (stateValues : List Int) →
  length stateValues ≡ length initialValues →
  (((currentHigh : Int) →
    (((firstHigh ≤Z currentHigh) ∧
      (currentHigh ≤Z rows m)) ∧
     InnerState
       m
       currentRow
       currentHigh
       stateRowLow
       stateRowHigh
       stateColumnLow
       stateColumnHigh
       maximum
       stateValues) →
    ColumnLoopVC
      m
      currentRow
      currentHigh
      stateRowLow
      stateRowHigh
      stateColumnLow
      stateColumnHigh
      maximum
      stateValues) ∧
   (InnerState
      m
      currentRow
      (addInt (rows m) oneZ)
      stateRowLow
      stateRowHigh
      stateColumnLow
      stateColumnHigh
      maximum
      stateValues →
    OuterState
      m
      (addInt currentRow oneZ)
      stateRowLow
      stateRowHigh
      stateColumnLow
      stateColumnHigh
      maximum))

InnerLoopVC :
  Matrix →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  List Int →
  Set
InnerLoopVC
  m currentRow
  stateRowLow stateRowHigh stateColumnLow stateColumnHigh maximum
  values =
  let firstHigh = addInt currentRow oneZ
      afterLastHigh = addInt (rows m) oneZ
  in
  (firstHigh ≤Z afterLastHigh →
   InnerState
     m
     currentRow
     firstHigh
     stateRowLow
     stateRowHigh
     stateColumnLow
     stateColumnHigh
     maximum
     values ∧
   InnerIterationObligations m currentRow firstHigh values) ∧
  (afterLastHigh <Z firstHigh →
   OuterState
     m
     (addInt currentRow oneZ)
     stateRowLow
     stateRowHigh
     stateColumnLow
     stateColumnHigh
     maximum)

OutsideFilledRange :
  List Int →
  List Int →
  Int →
  Set
OutsideFilledRange before after filledLength =
  (index : Int) →
  (((zeroZ ≤Z index) ∧ (index <Z zeroZ)) ∨
   ((addInt zeroZ filledLength ≤Z index) ∧
    (index <Z lengthZ after))) →
  nthInt after index ≡ nthInt before index

FilledWithZero :
  List Int →
  Int →
  Set
FilledWithZero values filledLength =
  (index : Int) →
  ((zeroZ ≤Z index) ∧
   (index <Z addInt zeroZ filledLength)) →
  nthInt values index ≡ zeroZ

FillThenInnerLoop :
  Matrix →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  List Int →
  Set
FillThenInnerLoop
  m currentRow
  stateRowLow stateRowHigh stateColumnLow stateColumnHigh maximum
  values =
  let filledLength = columns m
  in
  ((zeroZ ≤Z zeroZ) ∧
   (zeroZ ≤Z filledLength) ∧
   (addInt zeroZ filledLength ≤Z lengthZ values)) ∧
  ((filled : List Int) →
   length filled ≡ length values →
   OutsideFilledRange values filled filledLength ∧
   FilledWithZero filled filledLength →
   InnerLoopVC
     m
     currentRow
     stateRowLow
     stateRowHigh
     stateColumnLow
     stateColumnHigh
     maximum
     filled)

OuterIterationObligations :
  Matrix →
  Int →
  List Int →
  Set
OuterIterationObligations m upper initialValues =
  (stateColumnHigh stateColumnLow stateRowHigh stateRowLow maximum : Int) →
  (stateValues : List Int) →
  length stateValues ≡ length initialValues →
  (((currentRow : Int) →
    (((zeroZ ≤Z currentRow) ∧ (currentRow ≤Z upper)) ∧
     OuterState
       m
       currentRow
       stateRowLow
       stateRowHigh
       stateColumnLow
       stateColumnHigh
       maximum) →
    FillThenInnerLoop
      m
      currentRow
      stateRowLow
      stateRowHigh
      stateColumnLow
      stateColumnHigh
      maximum
      stateValues) ∧
   (OuterState
      m
      (addInt upper oneZ)
      stateRowLow
      stateRowHigh
      stateColumnLow
      stateColumnHigh
      maximum →
    FinalPostcondition
      m
      maximum
      stateRowLow
      stateRowHigh
      stateColumnLow
      stateColumnHigh))

InitialOuterState : Matrix → Set
InitialOuterState m =
  OuterState m zeroZ zeroZ zeroZ zeroZ zeroZ zeroZ

MaximumSubmatrixVC : Matrix → Set
MaximumSubmatrixVC m =
  let outerUpper = subtractInt (rows m) oneZ
  in
  zeroZ ≤Z columns m ∧
  ((initialValues : List Int) →
   FilledWithZero initialValues (columns m) ∧
   lengthZ initialValues ≡ columns m →
   ((zeroZ ≤Z addInt outerUpper oneZ →
     InitialOuterState m ∧
     OuterIterationObligations m outerUpper initialValues) ∧
    (addInt outerUpper oneZ <Z zeroZ →
     FinalPostcondition m zeroZ zeroZ zeroZ zeroZ zeroZ)))

maximum-submatrix'vc : Set
maximum-submatrix'vc =
  (m : Matrix) →
  MaximumSubmatrixVC m
