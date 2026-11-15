-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2021_shearsort_ShearSort_sort_columnqtvc: the verification
-- condition for copying one matrix column to an array, sorting it, and writing
-- it back while preserving the other columns and column multiplicities.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2021ShearsortShearSortSortColumnQtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
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

ifInt : Bool → Int → Int → Int
ifInt true when-true when-false = when-true
ifInt false when-true when-false = when-false

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

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = pos (length xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

nthInt : List Int → Int → Int
nthInt xs index = nthDefault zeroZ (toNat index) xs

setAt : {A : Set} → List A → Nat → A → List A
setAt [] index value = []
setAt (_ ∷ xs) zero value = value ∷ xs
setAt (x ∷ xs) (suc index) value =
  x ∷ setAt xs index value

updateFunction :
  (Int → Int) →
  Int →
  Int →
  Int →
  Int
updateFunction values index value query =
  ifInt (intEqual query index) value (values query)

updateMatrixFunction :
  (Int → Int → Int) →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int
updateMatrixFunction values row column value query-row query-column =
  ifInt
    (intEqual query-row row)
    (updateFunction (values row) column value query-column)
    (values query-row query-column)

record Matrix : Set where
  constructor matrix
  field
    rows             : Int
    columns          : Int
    elts             : Int → Int → Int
    rows-nonnegative : zeroZ ≤Z rows
    cols-nonnegative : zeroZ ≤Z columns

open Matrix

ValidIndex : Matrix → Int → Int → Set
ValidIndex m row column =
  (zeroZ ≤Z row ∧ row <Z rows m) ∧
  zeroZ ≤Z column ∧ column <Z columns m

Dimensions : Matrix → Matrix → Set
Dimensions current previous =
  rows current ≡ rows previous ∧
  columns current ≡ columns previous

column : Matrix → Int → Int → Int
column m j i = elts m i j

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

PrefixMatches :
  List Int →
  Matrix →
  Int →
  Int →
  Set
PrefixMatches values m selected-column upper =
  (k : Int) →
  zeroZ ≤Z k ∧ k <Z upper →
  nthInt values k ≡ elts m k selected-column

AllZero : List Int → Int → Set
AllZero values upper =
  (i : Int) →
  zeroZ ≤Z i ∧ i <Z upper →
  nthInt values i ≡ zeroZ

SortedList : List Int → Set
SortedList values =
  (i k : Int) →
  zeroZ ≤Z i ∧ i ≤Z k ∧ k <Z lengthZ values →
  nthInt values i ≤Z nthInt values k

SortedColumn : Matrix → Int → Set
SortedColumn m selected-column =
  (i k : Int) →
  zeroZ ≤Z i ∧ i ≤Z k ∧ k <Z rows m →
  elts m i selected-column ≤Z elts m k selected-column

OtherColumnsUnchanged :
  Matrix →
  Matrix →
  Int →
  Set
OtherColumnsUnchanged current original selected-column =
  (row column-index : Int) →
  ((zeroZ ≤Z row ∧ row <Z rows current) ∧
   (zeroZ ≤Z column-index ∧ column-index <Z columns current) ∧
   column-index ≠ selected-column) →
  elts current row column-index ≡
  elts original row column-index

ListUpdatePointwise :
  List Int →
  List Int →
  Int →
  Int →
  Set
ListUpdatePointwise updated previous index value =
  (query : Int) →
  nthInt updated query ≡
  updateFunction (nthInt previous) index value query

MatrixUpdatePointwise :
  Matrix →
  Matrix →
  Int →
  Int →
  Int →
  Set
MatrixUpdatePointwise updated previous row column-index value =
  (query-row query-column : Int) →
  elts updated query-row query-column ≡
  updateMatrixFunction
    (elts previous)
    row
    column-index
    value
    query-row
    query-column

ReadIteration :
  Matrix →
  Int →
  List Int →
  Int →
  Set
ReadIteration original selected-column current i =
  let last-row = subtractInt (rows original) oneZ
  in
  ((zeroZ ≤Z i ∧ i ≤Z last-row) ∧
   PrefixMatches current original selected-column i) →
  ValidIndex original i selected-column ∧
  (let value = elts original i selected-column
       updated = setAt current (toNat i) value
   in
   (zeroZ ≤Z i ∧ i <Z lengthZ current) ∧
   (length updated ≡ length current →
    ListUpdatePointwise updated current i value →
    PrefixMatches
      updated
      original
      selected-column
      (addInt i oneZ)))

WriteIteration :
  Matrix →
  Int →
  List Int →
  Matrix →
  Int →
  Set
WriteIteration original selected-column sorted-values current i =
  let last-row = subtractInt (rows original) oneZ
  in
  ((zeroZ ≤Z i ∧ i ≤Z last-row) ∧
   PrefixMatches sorted-values current selected-column i ∧
   OtherColumnsUnchanged current original selected-column) →
  (zeroZ ≤Z i ∧ i <Z lengthZ sorted-values) ∧
  ValidIndex current i selected-column ∧
  ((updated : Matrix) →
    Dimensions updated current →
    MatrixUpdatePointwise
      updated
      current
      i
      selected-column
      (nthInt sorted-values i) →
    PrefixMatches
      sorted-values
      updated
      selected-column
      (addInt i oneZ) ∧
    OtherColumnsUnchanged updated original selected-column)

WriteCompletion :
  Matrix →
  Int →
  List Int →
  Matrix →
  Set
WriteCompletion original selected-column sorted-values current =
  let last-row = subtractInt (rows original) oneZ
  in
  (PrefixMatches
     sorted-values
     current
     selected-column
     (addInt last-row oneZ) ∧
   OtherColumnsUnchanged current original selected-column) →
  OtherColumnsUnchanged current original selected-column ∧
  SortedColumn current selected-column ∧
  MapPermut
    (column current selected-column)
    (column original selected-column)
    zeroZ
    (rows current)

WriteBackVC :
  Matrix →
  Int →
  List Int →
  Set
WriteBackVC original selected-column sorted-values =
  let last-row = subtractInt (rows original) oneZ
      loop-upper = addInt last-row oneZ
  in
  (zeroZ ≤Z loop-upper →
    PrefixMatches sorted-values original selected-column zeroZ ∧
    ((current : Matrix) →
      Dimensions current original →
      ((i : Int) →
        WriteIteration
          original
          selected-column
          sorted-values
          current
          i) ∧
      WriteCompletion
        original
        selected-column
        sorted-values
        current)) ∧
  (loop-upper <Z zeroZ →
    SortedColumn original selected-column ∧
    MapPermut
      (column original selected-column)
      (column original selected-column)
      zeroZ
      (rows original))

AfterArraySort :
  Matrix →
  Int →
  List Int →
  Set
AfterArraySort original selected-column before-sort =
  (sorted-values : List Int) →
  length sorted-values ≡ length before-sort →
  (SortedList sorted-values ∧
   MapPermut
     (nthInt sorted-values)
     (nthInt before-sort)
     zeroZ
     (lengthZ sorted-values)) →
  WriteBackVC original selected-column sorted-values

ReadLoop :
  Matrix →
  Int →
  List Int →
  List Int →
  Set
ReadLoop original selected-column initial current =
  length current ≡ length initial →
  (((i : Int) →
      ReadIteration original selected-column current i) ∧
   (PrefixMatches
      current
      original
      selected-column
      (addInt (subtractInt (rows original) oneZ) oneZ) →
    AfterArraySort original selected-column current))

ColumnSortBody :
  Matrix →
  Int →
  Set
ColumnSortBody original selected-column =
  let row-count = rows original
      last-row = subtractInt row-count oneZ
      loop-upper = addInt last-row oneZ
  in
  zeroZ ≤Z row-count ∧
  ((initial : List Int) →
    (AllZero initial row-count ∧
     lengthZ initial ≡ row-count) →
    ((zeroZ ≤Z loop-upper →
      PrefixMatches initial original selected-column zeroZ ∧
      ((current : List Int) →
        ReadLoop original selected-column initial current)) ∧
     (loop-upper <Z zeroZ →
      ((sorted-values : List Int) →
        length sorted-values ≡ length initial →
        (SortedList sorted-values ∧
         MapPermut
           (nthInt sorted-values)
           (nthInt initial)
           zeroZ
           (lengthZ sorted-values)) →
        WriteBackVC original selected-column sorted-values))))

sort-column-vc : Set
sort-column-vc =
  (selected-column : Int) →
  (original : Matrix) →
  zeroZ ≤Z selected-column →
  selected-column <Z columns original →
  ColumnSortBody original selected-column
