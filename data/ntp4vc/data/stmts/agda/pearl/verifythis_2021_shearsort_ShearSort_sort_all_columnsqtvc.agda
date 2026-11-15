-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2021_shearsort_ShearSort_sort_all_columnsqtvc: the full
-- verification condition for sorting every column of an integer matrix,
-- including direct column iteration and transpose-based row iteration.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2021ShearsortShearSortSortAllColumnsQtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≠_ _≤Z_ _<Z_
infixr 3 _∧_
infixr 2 _∨_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

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

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value     : A
    satisfies : P value

ifSet : Bool → Set → Set → Set
ifSet true when-true when-false = when-true
ifSet false when-true when-false = when-false

ifNat : Bool → Nat → Nat → Nat
ifNat true when-true when-false = when-true
ifNat false when-true when-false = when-false

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

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

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

occurrences :
  Int →
  (Int → Int) →
  Int →
  Int →
  Int
occurrences sought values lower upper =
  pos
    (countFrom
      (λ index → intEqual (values index) sought)
      lower
      (toNat (subtractInt upper lower)))

MapPermut :
  (Int → Int) →
  (Int → Int) →
  Int →
  Int →
  Set
MapPermut first-map second-map lower upper =
  (value : Int) →
  occurrences value first-map lower upper ≡
  occurrences value second-map lower upper

column : Matrix → Int → Int → Int
column m j i = elts m i j

Dimensions : Matrix → Matrix → Set
Dimensions current previous =
  rows current ≡ rows previous ∧
  columns current ≡ columns previous

Square : Matrix → Set
Square m = rows m ≡ columns m

ColumnPermutedTo : Matrix → Matrix → Set
ColumnPermutedTo current original =
  (j : Int) →
  zeroZ ≤Z j ∧ j <Z columns current →
  MapPermut
    (column current j)
    (column original j)
    zeroZ
    (rows current)

ColumnsSortedBefore : Matrix → Int → Set
ColumnsSortedBefore current limit =
  (i j k : Int) →
  ((zeroZ ≤Z i ∧ i ≤Z k ∧ k <Z rows current) ∧
   zeroZ ≤Z j ∧ j <Z limit) →
  elts current i j ≤Z elts current k j

ColumnPost : Matrix → Matrix → Set
ColumnPost current original =
  ColumnPermutedTo current original ∧
  ColumnsSortedBefore current (columns current)

OtherColumnsUnchanged : Matrix → Matrix → Int → Set
OtherColumnsUnchanged current previous tid =
  (i k : Int) →
  (zeroZ ≤Z i ∧
   i <Z rows current ∧
   (zeroZ ≤Z k ∧ k <Z columns current) ∧
   k ≠ tid) →
  elts current i k ≡ elts previous i k

SelectedColumnSorted : Matrix → Int → Set
SelectedColumnSorted current tid =
  (i k : Int) →
  zeroZ ≤Z i ∧ i ≤Z k ∧ k <Z rows current →
  elts current i tid ≤Z elts current k tid

SelectedColumnPermuted : Matrix → Matrix → Int → Set
SelectedColumnPermuted current previous tid =
  MapPermut
    (column current tid)
    (column previous tid)
    zeroZ
    (rows current)

ColumnIterationResult :
  Matrix →
  Matrix →
  Int →
  Matrix →
  Set
ColumnIterationResult original previous tid current =
  OtherColumnsUnchanged current previous tid ∧
  SelectedColumnSorted current tid ∧
  SelectedColumnPermuted current previous tid →
  ColumnPermutedTo current original ∧
  ColumnsSortedBefore current (addInt tid oneZ)

ColumnIteration :
  Matrix →
  Matrix →
  Int →
  Set
ColumnIteration original previous tid =
  (zeroZ ≤Z tid ∧ tid <Z columns previous) ∧
  ((current : Matrix) →
    Dimensions current previous →
    ColumnIterationResult original previous tid current)

ColumnLoopIterations :
  Matrix →
  Matrix →
  Int →
  Set
ColumnLoopIterations original current upper =
  (tid : Int) →
  ((zeroZ ≤Z tid ∧ tid ≤Z upper) ∧
   ColumnPermutedTo current original ∧
   ColumnsSortedBefore current tid) →
  ColumnIteration original current tid

ColumnLoopCompletion :
  Matrix →
  Matrix →
  Int →
  Set
ColumnLoopCompletion original current upper =
  ColumnPermutedTo current original ∧
  ColumnsSortedBefore current (addInt upper oneZ) →
  ColumnPost current original

ColumnLoopVC :
  Matrix →
  Matrix →
  Int →
  Set
ColumnLoopVC original initial upper =
  (current : Matrix) →
  Dimensions current initial →
  ColumnLoopIterations original current upper ∧
  ColumnLoopCompletion original current upper

DirectColumnBranch : Matrix → Set
DirectColumnBranch original =
  let upper = subtractInt (columns original) oneZ
  in
  (zeroZ ≤Z addInt upper oneZ →
    (ColumnPermutedTo original original ∧
     ColumnsSortedBefore original zeroZ) ∧
    ColumnLoopVC original original upper) ∧
  (addInt upper oneZ <Z zeroZ →
    ColumnPost original original)

TransposeRelation : Matrix → Matrix → Set
TransposeRelation before after =
  (i j : Int) →
  ((zeroZ ≤Z i ∧ i <Z rows after) ∧
   zeroZ ≤Z j ∧ j <Z columns after) →
  elts before i j ≡ elts after j i

RowsPermutedFromColumns :
  Matrix →
  Matrix →
  Int →
  Set
RowsPermutedFromColumns current original n =
  (j : Int) →
  zeroZ ≤Z j ∧ j <Z n →
  MapPermut
    (elts current j)
    (column original j)
    zeroZ
    n

RowsSortedBefore :
  Matrix →
  Int →
  Int →
  Set
RowsSortedBefore current n limit =
  (i j k : Int) →
  ((zeroZ ≤Z i ∧ i ≤Z k ∧ k <Z n) ∧
   zeroZ ≤Z j ∧ j <Z limit) →
  elts current j i ≤Z elts current j k

OtherRowsUnchanged : Matrix → Matrix → Int → Set
OtherRowsUnchanged current previous tid =
  (j k : Int) →
  (zeroZ ≤Z j ∧
   j <Z rows current ∧
   (zeroZ ≤Z k ∧ k <Z columns current) ∧
   j ≠ tid) →
  elts current j k ≡ elts previous j k

SelectedRowSorted : Matrix → Int → Set
SelectedRowSorted current tid =
  (j k : Int) →
  zeroZ ≤Z j ∧ j ≤Z k ∧ k <Z columns current →
  elts current tid j ≤Z elts current tid k

SelectedRowPermuted : Matrix → Matrix → Int → Set
SelectedRowPermuted current previous tid =
  MapPermut
    (elts current tid)
    (elts previous tid)
    zeroZ
    (columns current)

RowIterationResult :
  Matrix →
  Matrix →
  Int →
  Int →
  Matrix →
  Set
RowIterationResult original previous n tid current =
  OtherRowsUnchanged current previous tid ∧
  SelectedRowSorted current tid ∧
  SelectedRowPermuted current previous tid →
  RowsPermutedFromColumns current original n ∧
  RowsSortedBefore current n (addInt tid oneZ)

RowIteration :
  Matrix →
  Matrix →
  Int →
  Int →
  Set
RowIteration original previous n tid =
  (zeroZ ≤Z tid ∧ tid <Z rows previous) ∧
  ((current : Matrix) →
    Dimensions current previous →
    RowIterationResult original previous n tid current)

RowLoopIterations :
  Matrix →
  Matrix →
  Int →
  Int →
  Set
RowLoopIterations original current n upper =
  (tid : Int) →
  ((zeroZ ≤Z tid ∧ tid ≤Z upper) ∧
   RowsPermutedFromColumns current original n ∧
   RowsSortedBefore current n tid) →
  RowIteration original current n tid

TransposeBackPost : Matrix → Matrix → Set
TransposeBackPost original row-sorted =
  Square row-sorted ∧
  ((transposed-back : Matrix) →
    Dimensions transposed-back row-sorted →
    TransposeRelation row-sorted transposed-back →
    ColumnPost transposed-back original)

RowLoopCompletion :
  Matrix →
  Matrix →
  Int →
  Int →
  Set
RowLoopCompletion original current n upper =
  RowsPermutedFromColumns current original n ∧
  RowsSortedBefore current n (addInt upper oneZ) →
  TransposeBackPost original current

RowLoopVC :
  Matrix →
  Matrix →
  Int →
  Int →
  Set
RowLoopVC original initial n upper =
  (current : Matrix) →
  Dimensions current initial →
  RowLoopIterations original current n upper ∧
  RowLoopCompletion original current n upper

EmptyTransposeLoop :
  Matrix →
  Matrix →
  Set
EmptyTransposeLoop original transposed =
  Square transposed ∧
  ((transposed-back : Matrix) →
    Dimensions transposed-back transposed →
    TransposeRelation transposed transposed-back →
    ColumnPost transposed-back original)

TransposeLoopBranch :
  Matrix →
  Matrix →
  Int →
  Set
TransposeLoopBranch original transposed n =
  let upper = subtractInt (columns transposed) oneZ
  in
  (zeroZ ≤Z addInt upper oneZ →
    (RowsPermutedFromColumns transposed original n ∧
     RowsSortedBefore transposed n zeroZ) ∧
    RowLoopVC original transposed n upper) ∧
  (addInt upper oneZ <Z zeroZ →
    EmptyTransposeLoop original transposed)

TransposeColumnBranch : Matrix → Set
TransposeColumnBranch original =
  let n = rows original
  in
  Square original ∧
  ((transposed : Matrix) →
    Dimensions transposed original →
    TransposeRelation original transposed →
    TransposeLoopBranch original transposed n)

SortAllColumnsVC : Matrix → Set
SortAllColumnsVC original =
  Exists Bool
    (λ result →
      result ≡ true ∨ Square original) ∧
  ((choice : Bool) →
    (choice ≡ true ∨ Square original) →
    ifSet choice
      (DirectColumnBranch original)
      (TransposeColumnBranch original))

sort-all-columns-vc : Set
sort-all-columns-vc =
  (original : Matrix) →
  SortAllColumnsVC original
