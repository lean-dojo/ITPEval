-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2021_shearsort_ShearSort_sort_all_rowsqtvc: the verification
-- condition for sorting every row of an integer matrix in alternating
-- ascending and descending order while preserving each row's multiset.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2021ShearsortShearSortSortAllRowsQtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≠_ _≤Z_ _<Z_
infixr 3 _∧_

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

modTwoNat : Nat → Nat
modTwoNat zero = zero
modTwoNat (suc zero) = suc zero
modTwoNat (suc (suc n)) = modTwoNat n

-- Why3's Euclidean remainder for the positive divisor two.
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

Dimensions : Matrix → Matrix → Set
Dimensions current previous =
  rows current ≡ rows previous ∧
  columns current ≡ columns previous

SnakeOrder :
  Matrix →
  Int →
  Int →
  Int →
  Set
SnakeOrder current row-index lower-column upper-column =
  ifSet
    (intEqual (modTwo row-index) zeroZ)
    (elts current row-index lower-column ≤Z
      elts current row-index upper-column)
    (elts current row-index upper-column ≤Z
      elts current row-index lower-column)

RowsPermutedTo : Matrix → Matrix → Set
RowsPermutedTo current original =
  (i : Int) →
  zeroZ ≤Z i ∧ i <Z rows current →
  MapPermut
    (elts current i)
    (elts original i)
    zeroZ
    (columns current)

RowsSortedBefore : Matrix → Int → Set
RowsSortedBefore current limit =
  (i j k : Int) →
  ((zeroZ ≤Z i ∧ i <Z limit) ∧
   zeroZ ≤Z j ∧ j ≤Z k ∧ k <Z columns current) →
  SnakeOrder current i j k

RowsPost : Matrix → Matrix → Set
RowsPost current original =
  RowsPermutedTo current original ∧
  RowsSortedBefore current (rows current)

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
  SnakeOrder current tid j k

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
  Matrix →
  Set
RowIterationResult original previous tid current =
  OtherRowsUnchanged current previous tid ∧
  SelectedRowSorted current tid ∧
  SelectedRowPermuted current previous tid →
  RowsPermutedTo current original ∧
  RowsSortedBefore current (addInt tid oneZ)

RowIteration :
  Matrix →
  Matrix →
  Int →
  Set
RowIteration original previous tid =
  twoZ ≠ zeroZ ∧
  (zeroZ ≤Z tid ∧ tid <Z rows previous) ∧
  ((current : Matrix) →
    Dimensions current previous →
    RowIterationResult original previous tid current)

RowLoopIterations :
  Matrix →
  Matrix →
  Int →
  Set
RowLoopIterations original current upper =
  (tid : Int) →
  ((zeroZ ≤Z tid ∧ tid ≤Z upper) ∧
   RowsPermutedTo current original ∧
   RowsSortedBefore current tid) →
  RowIteration original current tid

RowLoopCompletion :
  Matrix →
  Matrix →
  Int →
  Set
RowLoopCompletion original current upper =
  RowsPermutedTo current original ∧
  RowsSortedBefore current (addInt upper oneZ) →
  RowsPost current original

RowLoopVC :
  Matrix →
  Matrix →
  Int →
  Set
RowLoopVC original initial upper =
  (current : Matrix) →
  Dimensions current initial →
  RowLoopIterations original current upper ∧
  RowLoopCompletion original current upper

InitialState : Matrix → Set
InitialState original =
  RowsPermutedTo original original ∧
  RowsSortedBefore original zeroZ

SortAllRowsVC : Matrix → Set
SortAllRowsVC original =
  let upper = subtractInt (rows original) oneZ
  in
  (zeroZ ≤Z addInt upper oneZ →
    InitialState original ∧
    RowLoopVC original original upper) ∧
  (addInt upper oneZ <Z zeroZ →
    RowsPost original original)

sort-all-rows-vc : Set
sort-all-rows-vc =
  (original : Matrix) →
  SortAllRowsVC original
