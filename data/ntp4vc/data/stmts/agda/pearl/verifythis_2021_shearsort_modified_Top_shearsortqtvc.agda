-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2021_shearsort_modified_Top_shearsortqtvc: the verification
-- condition for modified in-place integer-matrix Shearsort, including row and
-- column loop invariants, inversion decrease, snake order, and multiplicity
-- preservation. This file contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2021ShearsortModifiedTopShearsortqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≠_ _≤Z_ _<Z_
infixr 3 _∧_
infixr 2 _∨_

data Bottom : Set where

Not : Set → Set
Not proposition = proposition → Bottom

_≠_ : {A : Set} → A → A → Set
x ≠ y = Not (x ≡ y)

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

ifSet : Bool → Set → Set → Set
ifSet true when-true when-false = when-true
ifSet false when-true when-false = when-false

ifBool : Bool → Bool → Bool → Bool
ifBool true when-true when-false = when-true
ifBool false when-true when-false = when-false

ifNat : Bool → Nat → Nat → Nat
ifNat true when-true when-false = when-true
ifNat false when-true when-false = when-false

notBool : Bool → Bool
notBool true = false
notBool false = true

andBool : Bool → Bool → Bool
andBool true second-bool = second-bool
andBool false second-bool = false

orBool : Bool → Bool → Bool
orBool true second-bool = true
orBool false second-bool = second-bool

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

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

modTwoNat : Nat → Nat
modTwoNat zero = zero
modTwoNat (suc zero) = suc zero
modTwoNat (suc (suc n)) = modTwoNat n

-- Why3's Euclidean remainder by the positive divisor two.
modTwo : Int → Int
modTwo (pos n) = pos (modTwoNat n)
modTwo (negsuc n) = pos (modTwoNat (suc n))

zeroZ oneZ twoZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))

record Matrix : Set where
  constructor matrix
  field
    rows             : Int
    columns          : Int
    elts             : Int → Int → Int
    rows-nonnegative : zeroZ ≤Z rows
    cols-nonnegative : zeroZ ≤Z columns

open Matrix

countFrom : (Int → Bool) → Int → Nat → Nat
countFrom predicate current zero = zero
countFrom predicate current (suc remaining) =
  ifNat
    (predicate current)
    (suc (countFrom predicate (addInt current oneZ) remaining))
    (countFrom predicate (addInt current oneZ) remaining)

numof : (Int → Bool) → Int → Int → Int
numof predicate lower upper =
  pos
    (countFrom
      predicate
      lower
      (toNat (subtractInt upper lower)))

occurrences : Int → (Int → Int) → Int → Int → Int
occurrences value values lower upper =
  numof
    (λ index → intEqual (values index) value)
    lower
    upper

sumOccurrencesRows :
  Int → Matrix → Nat → Nat → Nat
sumOccurrencesRows value m row-index zero = zero
sumOccurrencesRows value m row-index (suc remaining) =
  toNat
    (occurrences
      value
      (elts m (pos row-index))
      zeroZ
      (columns m))
  + sumOccurrencesRows value m (suc row-index) remaining

mocc : Int → Matrix → Int
mocc value m =
  pos
    (sumOccurrencesRows
      value
      m
      zero
      (toNat (rows m)))

ltIndexBool : Int → Int → Int → Int → Bool
ltIndexBool i j k l =
  orBool
    (intLess i k)
    (andBool
      (intEqual i k)
      (ifBool
        (intEqual (modTwo i) zeroZ)
        (intLess j l)
        (intLess l j)))

ltIndex : Int → Int → Int → Int → Set
ltIndex i j k l =
  i <Z k ∨
  (i ≡ k ∧
   ifSet
     (intEqual (modTwo i) zeroZ)
     (j <Z l)
     (l <Z j))

inversionAt : Matrix → Int → Int → Int → Int → Bool
inversionAt m i j k l =
  andBool
    (ltIndexBool i j k l)
    (intLess (elts m k l) (elts m i j))

countInversionColumns :
  Matrix → Int → Int → Int → Nat → Nat
countInversionColumns m i j k =
  countFrom
    (inversionAt m i j k)
    zeroZ

sumInversionRows :
  Matrix → Int → Int → Nat → Nat → Nat
sumInversionRows m i j row-index zero = zero
sumInversionRows m i j row-index (suc remaining) =
  countInversionColumns
    m i j (pos row-index) (toNat (columns m))
  + sumInversionRows m i j (suc row-index) remaining

sumInversionColumns :
  Matrix → Int → Nat → Nat → Nat
sumInversionColumns m i column-index zero = zero
sumInversionColumns m i column-index (suc remaining) =
  sumInversionRows
    m i (pos column-index) zero (toNat (rows m))
  + sumInversionColumns m i (suc column-index) remaining

sumInversions :
  Matrix → Nat → Nat → Nat
sumInversions m row-index zero = zero
sumInversions m row-index (suc remaining) =
  sumInversionColumns
    m (pos row-index) zero (toNat (columns m))
  + sumInversions m (suc row-index) remaining

inversions : Matrix → Int
inversions m =
  pos (sumInversions m zero (toNat (rows m)))

SameDimensions : Matrix → Matrix → Set
SameDimensions current previous =
  rows current ≡ rows previous ∧
  columns current ≡ columns previous

SameOccurrences : Matrix → Matrix → Set
SameOccurrences current previous =
  (value : Int) →
  mocc value current ≡ mocc value previous

AllCellsEqual : Matrix → Matrix → Set
AllCellsEqual current previous =
  (i j : Int) →
  zeroZ ≤Z i ∧ i <Z rows current →
  zeroZ ≤Z j ∧ j <Z columns current →
  elts current i j ≡ elts previous i j

RowFrame : Matrix → Matrix → Int → Set
RowFrame current previous selected-row =
  (i j : Int) →
  zeroZ ≤Z i ∧ i <Z rows current →
  zeroZ ≤Z j ∧ j <Z columns current →
  i ≠ selected-row →
  elts current i j ≡ elts previous i j

ColumnFrame : Matrix → Matrix → Int → Set
ColumnFrame current previous selected-column =
  (i j : Int) →
  zeroZ ≤Z i ∧ i <Z rows current →
  zeroZ ≤Z j ∧ j <Z columns current →
  j ≠ selected-column →
  elts current i j ≡ elts previous i j

ColumnUnchanged : Matrix → Matrix → Int → Set
ColumnUnchanged current previous selected-column =
  (i : Int) →
  zeroZ ≤Z i ∧ i <Z rows current →
  elts current i selected-column ≡
  elts previous i selected-column

sortedRow : Matrix → Int → Bool → Set
sortedRow m row ascending =
  (zeroZ ≤Z row ∧ row <Z rows m) ∧
  ifSet ascending
    ((j l : Int) →
      zeroZ ≤Z j ∧ j ≤Z l ∧ l <Z columns m →
      elts m row j ≤Z elts m row l)
    ((j l : Int) →
      zeroZ ≤Z j ∧ j ≤Z l ∧ l <Z columns m →
      elts m row l ≤Z elts m row j)

sortedColumn : Matrix → Int → Set
sortedColumn m column =
  (zeroZ ≤Z column ∧ column <Z columns m) ∧
  ((i k : Int) →
    zeroZ ≤Z i ∧ i ≤Z k ∧ k <Z rows m →
    elts m i column ≤Z elts m k column)

snakeOrder : Matrix → Set
snakeOrder m =
  (i j k l : Int) →
  zeroZ ≤Z i ∧ i <Z rows m →
  zeroZ ≤Z j ∧ j <Z columns m →
  zeroZ ≤Z k ∧ k <Z rows m →
  zeroZ ≤Z l ∧ l <Z columns m →
  ltIndex i j k l →
  elts m i j ≤Z elts m k l

OrderedOnSourceColumns : Matrix → Matrix → Set
OrderedOnSourceColumns source current =
  (i j k l : Int) →
  (zeroZ ≤Z i ∧ i <Z columns source) ∧
  (zeroZ ≤Z j ∧ j <Z columns source) ∧
  (zeroZ ≤Z k ∧ k <Z columns source) ∧
  (zeroZ ≤Z l ∧ l <Z columns source) ∧
  ltIndex i j k l →
  elts current i j ≤Z elts current k l

RowsSortedBefore : Matrix → Int → Set
RowsSortedBefore m upper =
  (k : Int) →
  zeroZ ≤Z k ∧ k <Z upper →
  sortedRow
    m
    k
    (intEqual (modTwo k) zeroZ)

ColumnsSortedBefore : Matrix → Int → Set
ColumnsSortedBefore m upper =
  (l : Int) →
  zeroZ ≤Z l ∧ l <Z upper →
  sortedColumn m l

RowSortPost : Matrix → Matrix → Int → Set
RowSortPost previous current selected-row =
  RowFrame current previous selected-row ∧
  SameOccurrences current previous ∧
  sortedRow
    current
    selected-row
    (intEqual (modTwo selected-row) zeroZ) ∧
  inversions current ≤Z inversions previous

RowLoopInvariant :
  Matrix → Matrix → Matrix → Int → Int → Set
RowLoopInvariant source row-anchor current i last-row =
  (zeroZ ≤Z i ∧ i ≤Z last-row) ∧
  RowsSortedBefore current i ∧
  SameOccurrences current source ∧
  inversions current ≤Z inversions row-anchor

RowIteration :
  Matrix → Matrix → Matrix → Int → Set
RowIteration source row-anchor current i =
  twoZ ≠ zeroZ ∧
  (zeroZ ≤Z i ∧ i <Z rows current) ∧
  ((next : Matrix) →
    SameDimensions next current →
    RowSortPost current next i →
    RowsSortedBefore next (addInt i oneZ) ∧
    SameOccurrences next source ∧
    inversions next ≤Z inversions row-anchor)

RowLoopObligations :
  Matrix → Matrix → Matrix → Int → Set
RowLoopObligations source row-anchor current last-row =
  (i : Int) →
  RowLoopInvariant source row-anchor current i last-row →
  RowIteration source row-anchor current i

RowExitInvariant :
  Matrix → Matrix → Matrix → Int → Set
RowExitInvariant source row-anchor current last-row =
  RowsSortedBefore current (addInt last-row oneZ) ∧
  SameOccurrences current source ∧
  inversions current ≤Z inversions row-anchor

ColumnSortPost :
  Matrix → Matrix → Int → Bool → Set
ColumnSortPost previous current selected-column unchanged =
  ColumnFrame current previous selected-column ∧
  SameOccurrences current previous ∧
  (unchanged ≡ true →
    ColumnUnchanged current previous selected-column) ∧
  sortedColumn current selected-column ∧
  inversions current ≤Z inversions previous ∧
  (Not (unchanged ≡ true) →
    inversions current <Z inversions previous)

ColumnStepResult :
  Matrix → Matrix → Matrix → Int → Bool → Bool → Set
ColumnStepResult
  source phase-anchor next selected-column nochange unchanged =
  ifSet (notBool unchanged)
    ((false ≡ true →
      AllCellsEqual next phase-anchor) ∧
     ColumnsSortedBefore next (addInt selected-column oneZ) ∧
     SameOccurrences next source ∧
     inversions next ≤Z inversions phase-anchor ∧
     (Not (false ≡ true) →
       inversions next <Z inversions phase-anchor))
    ((nochange ≡ true →
      AllCellsEqual next phase-anchor) ∧
     ColumnsSortedBefore next (addInt selected-column oneZ) ∧
     SameOccurrences next source ∧
     inversions next ≤Z inversions phase-anchor ∧
     (Not (nochange ≡ true) →
       inversions next <Z inversions phase-anchor))

ColumnLoopInvariant :
  Matrix → Matrix → Matrix → Bool → Int → Int → Set
ColumnLoopInvariant
  source phase-anchor current nochange selected-column last-column =
  (zeroZ ≤Z selected-column ∧ selected-column ≤Z last-column) ∧
  (nochange ≡ true →
    AllCellsEqual current phase-anchor) ∧
  ColumnsSortedBefore current selected-column ∧
  SameOccurrences current source ∧
  inversions current ≤Z inversions phase-anchor ∧
  (Not (nochange ≡ true) →
    inversions current <Z inversions phase-anchor)

ColumnIteration :
  Matrix → Matrix → Matrix → Bool → Int → Set
ColumnIteration source phase-anchor current nochange selected-column =
  (zeroZ ≤Z selected-column ∧
   selected-column <Z columns current) ∧
  ((next : Matrix) →
    SameDimensions next current →
    (unchanged : Bool) →
    ColumnSortPost current next selected-column unchanged →
    ColumnStepResult
      source
      phase-anchor
      next
      selected-column
      nochange
      unchanged)

ColumnLoopObligations :
  Matrix → Matrix → Matrix → Bool → Int → Set
ColumnLoopObligations source phase-anchor current nochange last-column =
  (selected-column : Int) →
  ColumnLoopInvariant
    source
    phase-anchor
    current
    nochange
    selected-column
    last-column →
  ColumnIteration
    source
    phase-anchor
    current
    nochange
    selected-column

ColumnExitInvariant :
  Matrix → Matrix → Matrix → Bool → Int → Set
ColumnExitInvariant source phase-anchor current nochange last-column =
  (nochange ≡ true →
    AllCellsEqual current phase-anchor) ∧
  ColumnsSortedBefore current (addInt last-column oneZ) ∧
  SameOccurrences current source ∧
  inversions current ≤Z inversions phase-anchor ∧
  (Not (nochange ≡ true) →
    inversions current <Z inversions phase-anchor)

ColumnExitConclusion :
  Matrix → Matrix → Matrix → Bool → Set
ColumnExitConclusion source row-anchor current nochange =
  ifSet nochange
    (OrderedOnSourceColumns source current ∧
     snakeOrder current ∧
     SameOccurrences current source)
    ((zeroZ ≤Z inversions row-anchor ∧
      inversions current <Z inversions row-anchor) ∧
     SameOccurrences current source)

ColumnExit :
  Matrix → Matrix → Matrix → Matrix → Bool → Int → Set
ColumnExit
  source row-anchor phase-anchor current nochange last-column =
  ColumnExitInvariant
    source
    phase-anchor
    current
    nochange
    last-column →
  ColumnExitConclusion source row-anchor current nochange

ColumnInitial : Matrix → Matrix → Set
ColumnInitial source phase-anchor =
  ColumnsSortedBefore phase-anchor zeroZ ∧
  SameOccurrences phase-anchor source ∧
  inversions phase-anchor ≤Z inversions phase-anchor

ColumnPhase : Matrix → Matrix → Matrix → Set
ColumnPhase source row-anchor phase-anchor =
  let last-column = subtractInt (columns source) oneZ
  in
  (zeroZ ≤Z addInt last-column oneZ →
    ColumnInitial source phase-anchor ∧
    ((nochange : Bool) →
     (current : Matrix) →
     SameDimensions current phase-anchor →
     ColumnLoopObligations
       source
       phase-anchor
       current
       nochange
       last-column ∧
     ColumnExit
       source
       row-anchor
       phase-anchor
       current
       nochange
       last-column)) ∧
  (addInt last-column oneZ <Z zeroZ →
    OrderedOnSourceColumns source phase-anchor ∧
    snakeOrder phase-anchor ∧
    SameOccurrences phase-anchor source)

RowInitial : Matrix → Matrix → Set
RowInitial source row-anchor =
  RowsSortedBefore row-anchor zeroZ ∧
  SameOccurrences row-anchor source ∧
  inversions row-anchor ≤Z inversions row-anchor

RowPhase : Matrix → Matrix → Int → Set
RowPhase source row-anchor last-row =
  RowInitial source row-anchor ∧
  ((current : Matrix) →
    SameDimensions current row-anchor →
    RowLoopObligations source row-anchor current last-row ∧
    (RowExitInvariant source row-anchor current last-row →
      ColumnPhase source row-anchor current))

ShearsortVC : Matrix → Matrix → Set
ShearsortVC source row-anchor =
  rows source ≡ columns source →
  rows row-anchor ≡ rows source →
  columns row-anchor ≡ columns source →
  SameOccurrences row-anchor source →
  let last-row = subtractInt (columns source) oneZ
  in
  (zeroZ ≤Z addInt last-row oneZ →
    RowPhase source row-anchor last-row) ∧
  (addInt last-row oneZ <Z zeroZ →
    ColumnPhase source row-anchor row-anchor)

shearsort'vc : Set
shearsort'vc =
  (source row-anchor : Matrix) →
  ShearsortVC source row-anchor
