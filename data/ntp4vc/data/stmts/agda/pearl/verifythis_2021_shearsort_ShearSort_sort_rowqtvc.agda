-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2021_shearsort_ShearSort_sort_rowqtvc: the verification
-- condition for copying one integer-matrix row to an array, sorting and
-- optionally reversing it, and writing it back. This file contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2021ShearsortShearSortSortRowQtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
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

ifSet : Bool → Set → Set → Set
ifSet true when-true when-false = when-true
ifSet false when-true when-false = when-false

ifInt : Bool → Int → Int → Int
ifInt true when-true when-false = when-true
ifInt false when-true when-false = when-false

ifNat : Bool → Nat → Nat → Nat
ifNat true when-true when-false = when-true
ifNat false when-true when-false = when-false

notBool : Bool → Bool
notBool true = false
notBool false = true

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
PrefixMatches values m selected-row upper =
  (column-index : Int) →
  zeroZ ≤Z column-index ∧ column-index <Z upper →
  nthInt values column-index ≡
  elts m selected-row column-index

AllZero : List Int → Int → Set
AllZero values upper =
  (index : Int) →
  zeroZ ≤Z index ∧ index <Z upper →
  nthInt values index ≡ zeroZ

SortedList : List Int → Set
SortedList values =
  (left right : Int) →
  zeroZ ≤Z left ∧ left ≤Z right ∧ right <Z lengthZ values →
  nthInt values left ≤Z nthInt values right

SelectedRowSorted : Matrix → Int → Bool → Set
SelectedRowSorted m selected-row ascending =
  (left right : Int) →
  zeroZ ≤Z left ∧ left ≤Z right ∧ right <Z columns m →
  ifSet
    ascending
    (elts m selected-row left ≤Z elts m selected-row right)
    (elts m selected-row right ≤Z elts m selected-row left)

OtherRowsUnchanged :
  Matrix →
  Matrix →
  Int →
  Set
OtherRowsUnchanged current original selected-row =
  (row column-index : Int) →
  ((zeroZ ≤Z row ∧ row <Z rows current) ∧
   (zeroZ ≤Z column-index ∧ column-index <Z columns current) ∧
   row ≠ selected-row) →
  elts current row column-index ≡
  elts original row column-index

FinalContract :
  Matrix →
  Matrix →
  Int →
  Bool →
  Set
FinalContract current original selected-row ascending =
  OtherRowsUnchanged current original selected-row ∧
  SelectedRowSorted current selected-row ascending ∧
  MapPermut
    (elts current selected-row)
    (elts original selected-row)
    zeroZ
    (columns current)

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

WriteIteration :
  List Int →
  Matrix →
  Int →
  Matrix →
  Int →
  Set
WriteIteration values original selected-row current column-index =
  let upper = subtractInt (columns original) oneZ
  in
  ((zeroZ ≤Z column-index ∧ column-index ≤Z upper) ∧
   PrefixMatches values current selected-row column-index ∧
   OtherRowsUnchanged current original selected-row) →
  (zeroZ ≤Z column-index ∧ column-index <Z lengthZ values) ∧
  ValidIndex current selected-row column-index ∧
  ((updated : Matrix) →
    Dimensions updated current →
    MatrixUpdatePointwise
      updated
      current
      selected-row
      column-index
      (nthInt values column-index) →
    PrefixMatches
      values
      updated
      selected-row
      (addInt column-index oneZ) ∧
    OtherRowsUnchanged updated original selected-row)

WriteCompletion :
  List Int →
  Matrix →
  Int →
  Bool →
  Matrix →
  Set
WriteCompletion values original selected-row ascending current =
  let upper = subtractInt (columns original) oneZ
  in
  (PrefixMatches
     values
     current
     selected-row
     (addInt upper oneZ) ∧
   OtherRowsUnchanged current original selected-row) →
  FinalContract current original selected-row ascending

WriteBackVC :
  List Int →
  Matrix →
  Int →
  Bool →
  Set
WriteBackVC values original selected-row ascending =
  let upper = subtractInt (columns original) oneZ
      loop-upper = addInt upper oneZ
  in
  (zeroZ ≤Z loop-upper →
    PrefixMatches values original selected-row zeroZ ∧
    ((current : Matrix) →
      Dimensions current original →
      ((column-index : Int) →
        WriteIteration
          values
          original
          selected-row
          current
          column-index) ∧
      WriteCompletion
        values
        original
        selected-row
        ascending
        current)) ∧
  (loop-upper <Z zeroZ →
    SelectedRowSorted original selected-row ascending ∧
    MapPermut
      (elts original selected-row)
      (elts original selected-row)
      zeroZ
      (columns original))

ReversalMiddle :
  List Int →
  List Int →
  Int →
  Int →
  Set
ReversalMiddle current sorted lower upper =
  (index : Int) →
  lower ≤Z index ∧ index ≤Z upper →
  nthInt current index ≡ nthInt sorted index

ReversalOutside :
  List Int →
  List Int →
  Int →
  Int →
  Set
ReversalOutside current sorted lower upper =
  (index : Int) →
  (zeroZ ≤Z index ∧ index <Z lower) ∨
  (upper <Z index ∧ index <Z lengthZ current) →
  nthInt current index ≡
  nthInt
    sorted
    (subtractInt
      (subtractInt (lengthZ current) oneZ)
      index)

ReversalInvariant :
  List Int →
  List Int →
  Int →
  Int →
  Set
ReversalInvariant current sorted lower upper =
  (zeroZ ≤Z lower ∧
   lower ≤Z addInt upper oneZ ∧
   addInt upper oneZ ≤Z lengthZ current) ∧
  addInt lower upper ≡ subtractInt (lengthZ current) oneZ ∧
  ReversalMiddle current sorted lower upper ∧
  ReversalOutside current sorted lower upper ∧
  MapPermut
    (nthInt sorted)
    (nthInt current)
    zeroZ
    (lengthZ current)

Exchange :
  List Int →
  List Int →
  Int →
  Int →
  Set
Exchange after before lower upper =
  ((zeroZ ≤Z lower ∧ lower <Z lengthZ after) ∧
   zeroZ ≤Z upper ∧ upper <Z lengthZ after) ∧
  ((index : Int) →
    ((zeroZ ≤Z index ∧ index ≤Z lengthZ after) ∧
     index ≠ lower ∧ index ≠ upper) →
    nthInt after index ≡ nthInt before index) ∧
  nthInt after lower ≡ nthInt before upper ∧
  nthInt after upper ≡ nthInt before lower

NextReversalInvariant :
  List Int →
  List Int →
  Int →
  Int →
  Set
NextReversalInvariant after sorted lower upper =
  (zeroZ ≤Z subtractInt upper lower ∧
   subtractInt
     (subtractInt upper oneZ)
     (addInt lower oneZ)
     <Z subtractInt upper lower) ∧
  ReversalInvariant
    after
    sorted
    (addInt lower oneZ)
    (subtractInt upper oneZ)

ReversalStep :
  List Int →
  List Int →
  Matrix →
  Int →
  Bool →
  Int →
  Int →
  Set
ReversalStep current sorted original selected-row ascending lower upper =
  ifSet
    (intLess lower upper)
    ((zeroZ ≤Z upper ∧ upper <Z lengthZ current) ∧
     (let temporary = nthInt current upper
      in
      (zeroZ ≤Z lower ∧ lower <Z lengthZ current) ∧
      (let lower-value = nthInt current lower
           after-upper = setAt current (toNat upper) lower-value
       in
       (zeroZ ≤Z upper ∧ upper <Z lengthZ current) ∧
       (length after-upper ≡ length current →
        ListUpdatePointwise
          after-upper
          current
          upper
          lower-value →
        (zeroZ ≤Z lower ∧ lower <Z lengthZ after-upper) ∧
        (let after = setAt after-upper (toNat lower) temporary
         in
         length after ≡ length after-upper →
         ListUpdatePointwise
           after
           after-upper
           lower
           temporary →
         Exchange after current lower upper ∧
         (MapPermut
           (nthInt after)
           (nthInt current)
           zeroZ
           (lengthZ after) →
          NextReversalInvariant
            after
            sorted
            lower
            upper))))))
    (WriteBackVC current original selected-row ascending)

ReversalVC :
  List Int →
  Matrix →
  Int →
  Bool →
  Set
ReversalVC sorted original selected-row ascending =
  let upper = subtractInt (lengthZ sorted) oneZ
  in
  ReversalInvariant sorted sorted zeroZ upper ∧
  ((v u : Int) →
    (current : List Int) →
    length current ≡ length sorted →
    ReversalInvariant current sorted u v →
    ReversalStep
      current
      sorted
      original
      selected-row
      ascending
      u
      v)

AfterSort :
  List Int →
  Matrix →
  Int →
  Bool →
  Set
AfterSort sorted original selected-row ascending =
  ifSet
    (notBool ascending)
    (ReversalVC sorted original selected-row ascending)
    (WriteBackVC sorted original selected-row ascending)

AllSortedResults :
  List Int →
  Matrix →
  Int →
  Bool →
  Set
AllSortedResults before-sort original selected-row ascending =
  (sorted : List Int) →
  length sorted ≡ length before-sort →
  (SortedList sorted ∧
   MapPermut
     (nthInt sorted)
     (nthInt before-sort)
     zeroZ
     (lengthZ sorted)) →
  AfterSort sorted original selected-row ascending

ReadIteration :
  Matrix →
  Int →
  List Int →
  Int →
  Set
ReadIteration original selected-row current column-index =
  let upper = subtractInt (columns original) oneZ
  in
  ((zeroZ ≤Z column-index ∧ column-index ≤Z upper) ∧
   PrefixMatches current original selected-row column-index) →
  ValidIndex original selected-row column-index ∧
  (let value = elts original selected-row column-index
       updated = setAt current (toNat column-index) value
   in
   (zeroZ ≤Z column-index ∧ column-index <Z lengthZ current) ∧
   (length updated ≡ length current →
    ListUpdatePointwise updated current column-index value →
    PrefixMatches
      updated
      original
      selected-row
      (addInt column-index oneZ)))

ReadLoop :
  Matrix →
  Int →
  Bool →
  List Int →
  List Int →
  Set
ReadLoop original selected-row ascending initial current =
  length current ≡ length initial →
  (((column-index : Int) →
      ReadIteration original selected-row current column-index) ∧
   (PrefixMatches
      current
      original
      selected-row
      (addInt (subtractInt (columns original) oneZ) oneZ) →
    AllSortedResults current original selected-row ascending))

CopyAndSortVC :
  List Int →
  Matrix →
  Int →
  Bool →
  Set
CopyAndSortVC initial original selected-row ascending =
  let upper = subtractInt (columns original) oneZ
      loop-upper = addInt upper oneZ
  in
  (zeroZ ≤Z loop-upper →
    PrefixMatches initial original selected-row zeroZ ∧
    ((current : List Int) →
      ReadLoop
        original
        selected-row
        ascending
        initial
        current)) ∧
  (loop-upper <Z zeroZ →
    AllSortedResults initial original selected-row ascending)

RowSortBody : Matrix → Int → Bool → Set
RowSortBody original selected-row ascending =
  let column-count = columns original
  in
  zeroZ ≤Z column-count ∧
  ((initial : List Int) →
    (AllZero initial column-count ∧
     lengthZ initial ≡ column-count) →
    CopyAndSortVC initial original selected-row ascending)

sort-row-vc : Set
sort-row-vc =
  (selected-row : Int) →
  (original : Matrix) →
  (ascending : Bool) →
  zeroZ ≤Z selected-row →
  selected-row <Z rows original →
  RowSortBody original selected-row ascending
