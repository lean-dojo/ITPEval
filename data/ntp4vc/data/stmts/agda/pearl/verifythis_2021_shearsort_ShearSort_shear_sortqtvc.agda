-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2021_shearsort_ShearSort_shear_sortqtvc: the verification
-- condition for in-place integer-matrix ShearSort, including logarithmic
-- rounds, alternating row order, column order, and multiset preservation.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2021ShearsortShearSortShearSortQtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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

record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open Pair

ifSet : Bool → Set → Set → Set
ifSet true A B = A
ifSet false A B = B

ifNat : Bool → Nat → Nat → Nat
ifNat true m n = m
ifNat false m n = n

ifInt : Bool → Int → Int → Int
ifInt true m n = m
ifInt false m n = n

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

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) = negateInt (pos (m * suc n))
multiplyInt (negsuc m) (pos n) = negateInt (pos (suc m * n))
multiplyInt (negsuc m) (negsuc n) = pos (suc m * suc n)

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

powerNat : Int → Nat → Int
powerNat base zero = pos (suc zero)
powerNat base (suc exponent) =
  multiplyInt base (powerNat base exponent)

powerInt : Int → Int → Int
powerInt base exponent = powerNat base (toNat exponent)

halfNat : Nat → Nat
halfNat zero = zero
halfNat (suc zero) = zero
halfNat (suc (suc n)) = suc (halfNat n)

modTwoNat : Nat → Nat
modTwoNat zero = zero
modTwoNat (suc zero) = suc zero
modTwoNat (suc (suc n)) = modTwoNat n

-- Why3's Euclidean quotient and remainder by the positive divisor two.
divTwo : Int → Int
divTwo (pos n) = pos (halfNat n)
divTwo (negsuc n) = negative (halfNat (suc (suc n)))

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
countFrom p current zero = zero
countFrom p current (suc remaining) =
  ifNat (p current)
    (suc (countFrom p (addInt current oneZ) remaining))
    (countFrom p (addInt current oneZ) remaining)

numof : (Int → Bool) → Int → Int → Int
numof p lower upper =
  pos (countFrom p lower (toNat (subtractInt upper lower)))

belowCount :
  (Int → Int → Int) → Int → Int → Int → Int → Int
belowCount e column value lower upper =
  numof (λ row → intLessOrEqual (e row column) value) lower upper

aboveCount :
  (Int → Int → Int) → Int → Int → Int → Int → Int
aboveCount e column value lower upper =
  numof (λ row → intLess value (e row column)) lower upper

occurrences :
  Int → (Int → Int) → Int → Int → Int
occurrences value f lower upper =
  numof (λ index → intEqual (f index) value) lower upper

sumRows :
  Int → (Int → Int → Int) → Int → Nat → Nat → Nat
sumRows value e column-count row-index zero = zero
sumRows value e column-count row-index (suc remaining) =
  toNat
    (occurrences value (e (pos row-index)) zeroZ column-count)
  + sumRows value e column-count (suc row-index) remaining

mocc :
  Int → (Int → Int → Int) → Int → Int → Int
mocc value e row-count column-count =
  pos (sumRows value e column-count zero (toNat row-count))

MapPermut :
  (Int → Int) → (Int → Int) → Int → Int → Set
MapPermut first-map second-map lower upper =
  (value : Int) →
  occurrences value first-map lower upper ≡
  occurrences value second-map lower upper

Dimensions : Matrix → Matrix → Set
Dimensions current previous =
  rows current ≡ rows previous ∧ columns current ≡ columns previous

Zones :
  (Int → Int) → (Int → Int) → Int →
  Matrix → Int → Int → Set
Zones zeros ones width current n c =
  ((value : Int) →
    zeroZ ≤Z zeros value ∧
    zeros value ≤Z ones value ∧
    ones value ≤Z n) ∧
  ((value : Int) →
    ones value ≤Z addInt (zeros value) width) ∧
  ((value i j : Int) →
    (zeroZ ≤Z i ∧ i <Z zeros value) ∧
    (zeroZ ≤Z j ∧ j <Z c) →
    elts current i j ≤Z value) ∧
  ((value i j : Int) →
    (ones value ≤Z i ∧ i <Z n) ∧
    (zeroZ ≤Z j ∧ j <Z c) →
    value <Z elts current i j)

zeroFunction : Int → Int
zeroFunction value = zeroZ

constantFunction : Int → Int → Int
constantFunction n value = n

ExtremeZones : Int → Matrix → Int → Int → Set
ExtremeZones width current n c =
  Zones zeroFunction (constantFunction n) width current n c

CrossRows : Matrix → Int → Int → Set
CrossRows current n c =
  (i j1 j2 k : Int) →
  (zeroZ ≤Z i ∧ i <Z k ∧ k <Z n) ∧
  (zeroZ ≤Z j1 ∧ j1 <Z c) ∧
  (zeroZ ≤Z j2 ∧ j2 <Z c) →
  elts current i j1 ≤Z elts current k j2

SnakeRows : Matrix → Int → Int → Set
SnakeRows current n c =
  (i j k : Int) →
  (zeroZ ≤Z i ∧ i <Z n) ∧
  (zeroZ ≤Z j ∧ j ≤Z k ∧ k <Z c) →
  ifSet (intEqual (modTwo i) zeroZ)
    (elts current i j ≤Z elts current i k)
    (elts current i k ≤Z elts current i j)

ColumnSorted : Matrix → Int → Int → Set
ColumnSorted current n c =
  (i j k : Int) →
  (zeroZ ≤Z i ∧ i ≤Z k ∧ k <Z n) ∧
  (zeroZ ≤Z j ∧ j <Z c) →
  elts current i j ≤Z elts current k j

RowPermuted : Matrix → Matrix → Set
RowPermuted current previous =
  (i : Int) →
  zeroZ ≤Z i ∧ i <Z rows current →
  MapPermut
    (elts current i)
    (elts previous i)
    zeroZ
    (columns current)

ColumnPermuted : Matrix → Matrix → Set
ColumnPermuted current previous =
  (j : Int) →
  zeroZ ≤Z j ∧ j <Z columns current →
  MapPermut
    (λ i → elts current i j)
    (λ i → elts previous i j)
    zeroZ
    (rows current)

PreservesOccurrences :
  Matrix → Matrix → Int → Int → Set
PreservesOccurrences original current n c =
  (value : Int) →
  mocc value (elts original) n c ≡
  mocc value (elts current) n c

PowerBounds : Int → Int → Int → Set
PowerBounds k exponent n =
  multiplyInt (subtractInt k oneZ) (powerInt twoZ exponent) <Z n ∧
  n ≤Z multiplyInt k (powerInt twoZ exponent)

FinalMatrixPost : Matrix → Matrix → Set
FinalMatrixPost original current =
  CrossRows current (rows current) (columns current) ∧
  SnakeRows current (rows current) (columns current) ∧
  PreservesOccurrences
    original current (rows current) (columns current)

Ascending : (Int → Int) → Int → Set
Ascending row c =
  (j k : Int) →
  zeroZ ≤Z j ∧ j ≤Z k ∧ k <Z c →
  row j ≤Z row k

Descending : (Int → Int) → Int → Set
Descending row c =
  (j k : Int) →
  zeroZ ≤Z j ∧ j ≤Z k ∧ k <Z c →
  row k ≤Z row j

OrBelow :
  (Int → Int) → (Int → Int) → Int → Int → Set
OrBelow first-row second-row value c =
  (i : Int) →
  zeroZ ≤Z i ∧ i <Z c →
  first-row i ≤Z value ∨ second-row i ≤Z value

OrAbove :
  (Int → Int) → (Int → Int) → Int → Int → Set
OrAbove first-row second-row value c =
  (i : Int) →
  zeroZ ≤Z i ∧ i <Z c →
  value <Z first-row i ∨ value <Z second-row i

ComparatorResultSymmetry :
  (Int → Int) → (Int → Int) → Int → Int → Set
ComparatorResultSymmetry r1 r2 value c =
  (result : Bool) →
  ((result ≡ true → OrBelow r2 r1 value c) ∧
   (result ≠ true → OrAbove r2 r1 value c)) →
  (result ≡ true → OrBelow r1 r2 value c) ∧
  (result ≠ true → OrAbove r1 r2 value c)

ComparatorScan :
  (Int → Int) → (Int → Int) → Int → Int → Set
ComparatorScan r1 r2 value c =
  (i : Int) →
    (zeroZ ≤Z i ∧ i ≤Z c) ∧
    ((j : Int) →
      zeroZ ≤Z j ∧ j <Z i →
      r1 j ≤Z value ∧ value <Z r2 j) →
    (outcome : Bool) →
    ifSet (notBool (intEqual i c))
      (ifSet (intLessOrEqual (r1 i) value)
        (outcome ≡ intLess value (r2 i))
        (outcome ≡ false))
      (outcome ≡ false) →
    ifSet outcome
      (((zeroZ ≤Z subtractInt c i) ∧
        subtractInt c (addInt i oneZ) <Z subtractInt c i) ∧
       (zeroZ ≤Z addInt i oneZ ∧ addInt i oneZ ≤Z c) ∧
       ((j : Int) →
         zeroZ ≤Z j ∧ j <Z addInt i oneZ →
         r1 j ≤Z value ∧ value <Z r2 j))
      ((result : Bool) →
        ifSet (intEqual i c)
          (result ≡ true)
          (result ≡ intLessOrEqual (r2 i) value) →
        (result ≡ true → OrBelow r1 r2 value c) ∧
        (result ≠ true → OrAbove r1 r2 value c))

ComparatorVC : Int → Int → Set
ComparatorVC c value =
  (r1 r2 : Int → Int) (orientation : Bool) →
  ((j k : Int) →
    zeroZ ≤Z j ∧ j ≤Z k ∧ k <Z c →
    ifSet orientation (r1 j ≤Z r1 k) (r1 k ≤Z r1 j)) ∧
  ((j k : Int) →
    zeroZ ≤Z j ∧ j ≤Z k ∧ k <Z c →
    ifSet orientation (r2 k ≤Z r2 j) (r2 j ≤Z r2 k)) →
  ifSet (notBool orientation)
    ((((zeroZ ≤Z ifInt orientation zeroZ oneZ) ∧
       zeroZ <Z ifInt orientation zeroZ oneZ) ∧
      Ascending r2 c ∧ Descending r1 c) ∧
     ComparatorResultSymmetry r1 r2 value c)
    (((zeroZ ≤Z zeroZ ∧ zeroZ ≤Z c) ∧
      ((j : Int) →
        zeroZ ≤Z j ∧ j <Z zeroZ →
        r1 j ≤Z value ∧ value <Z r2 j)) ∧
     ComparatorScan r1 r2 value c)

SelectionInvariant :
  (Int → Int → Int) →
  Int → Int → Int → Int → Int → Int → Int → Int → Set
SelectionInvariant e value z o index no nz n c =
  (z ≤Z index ∧ index ≤Z o) ∧
  (z ≤Z nz ∧ no ≤Z o) ∧
  subtractInt index z ≡
    multiplyInt twoZ
      (addInt (subtractInt nz z) (subtractInt o no)) ∧
  ((j : Int) →
    zeroZ ≤Z j ∧ j <Z c →
    nz ≤Z belowCount e j value zeroZ index ∧
    subtractInt n no ≤Z
      addInt
        (aboveCount e j value zeroZ index)
        (aboveCount e j value o n))

SelectionInitial :
  (Int → Int → Int) → Int → Int → Int → Int → Int → Set
SelectionInitial e value z o n c =
  ((z ≤Z z ∧ z ≤Z o) ∧
   (z ≤Z z ∧ o ≤Z o) ∧
   subtractInt z z ≡
     multiplyInt twoZ
       (addInt (subtractInt z z) (subtractInt o o)) ∧
   ((j : Int) →
     zeroZ ≤Z j ∧ j <Z c →
     z ≤Z belowCount e j value zeroZ z ∧
     subtractInt n o ≤Z
       addInt
         (aboveCount e j value zeroZ z)
         (aboveCount e j value o n)))

SelectionExit :
  (Int → Int → Int) →
  Int → Int → Int → Int → Int → Int → Set
SelectionExit e value nz no kd n c =
  (zeroZ ≤Z nz ∧ nz ≤Z no ∧ no ≤Z n) ∧
  no ≤Z addInt nz kd ∧
  ((j : Int) →
    zeroZ ≤Z j ∧ j <Z c →
    nz ≤Z belowCount e j value zeroZ n ∧
    subtractInt n no ≤Z aboveCount e j value zeroZ n)

SelectionPairStep :
  (Int → Int → Int) →
  Int → Int → Int → Int → Int → Int → Int → Int → Set
SelectionPairStep e value z o index no nz n c =
  let parity = modTwo index
      next-row = e (addInt index oneZ)
      this-row = e index
  in
  (ifSet (intEqual parity zeroZ)
     (Ascending this-row c)
     (Descending this-row c) ∧
   ifSet (intEqual parity zeroZ)
     (Descending next-row c)
     (Ascending next-row c)) ∧
  ((outcome : Bool) →
    ((outcome ≡ true →
      OrBelow this-row next-row value c) ∧
     (outcome ≠ true →
      OrAbove this-row next-row value c)) →
    ifSet outcome
      (((zeroZ ≤Z subtractInt o index ∧
         subtractInt o (addInt index twoZ) <Z
           subtractInt o index) ∧
        (z ≤Z addInt index twoZ ∧
         addInt index twoZ ≤Z o) ∧
        (z ≤Z addInt nz oneZ ∧ no ≤Z o) ∧
        subtractInt (addInt index twoZ) z ≡
          multiplyInt twoZ
            (addInt
              (subtractInt (addInt nz oneZ) z)
              (subtractInt o no)) ∧
        ((j : Int) →
          zeroZ ≤Z j ∧ j <Z c →
          addInt nz oneZ ≤Z
            belowCount e j value zeroZ (addInt index twoZ) ∧
          subtractInt n no ≤Z
            addInt
              (aboveCount e j value zeroZ (addInt index twoZ))
              (aboveCount e j value o n))))
      (((zeroZ ≤Z subtractInt o index ∧
         subtractInt o (addInt index twoZ) <Z
           subtractInt o index) ∧
        (z ≤Z addInt index twoZ ∧
         addInt index twoZ ≤Z o) ∧
        (z ≤Z nz ∧ subtractInt no oneZ ≤Z o) ∧
        subtractInt (addInt index twoZ) z ≡
          multiplyInt twoZ
            (addInt
              (subtractInt nz z)
              (subtractInt o (subtractInt no oneZ))) ∧
        ((j : Int) →
          zeroZ ≤Z j ∧ j <Z c →
          nz ≤Z
            belowCount e j value zeroZ (addInt index twoZ) ∧
          subtractInt n (subtractInt no oneZ) ≤Z
            addInt
              (aboveCount e j value zeroZ (addInt index twoZ))
              (aboveCount e j value o n)))))

SelectionLoop :
  (Int → Int → Int) →
  Int → Int → Int → Int → Int → Int → Set
SelectionLoop e value z o kd n c =
  (index no nz : Int) →
  SelectionInvariant e value z o index no nz n c →
  ifSet (intLess (addInt index oneZ) o)
    (ComparatorVC c value ∧
     twoZ ≠ zeroZ ∧
     SelectionPairStep e value z o index no nz n c)
    (SelectionExit e value nz no kd n c)

NzoProperty :
  (Int → Int → Int) → Int → Int → Int → Int →
  Pair Int Int → Set
NzoProperty e value kd n c bounds =
  let nz = fst bounds
      no = snd bounds
  in
  (zeroZ ≤Z nz ∧ nz ≤Z no ∧ no ≤Z n) ∧
  no ≤Z addInt nz kd ∧
  ((j : Int) →
    zeroZ ≤Z j ∧ j <Z c →
    nz ≤Z belowCount e j value zeroZ n ∧
    subtractInt n no ≤Z aboveCount e j value zeroZ n)

BelowColumnProgress :
  Matrix → Int → Int → Set
BelowColumnProgress current n c =
  (value i j : Int) →
  (zeroZ ≤Z i ∧ i <Z n) ∧
  (zeroZ <Z
     belowCount (elts current) j value (addInt i oneZ) n ∧
   zeroZ ≤Z j ∧ j <Z c) ∧
  value <Z elts current i j →
  let next = addInt i oneZ
  in
  (zeroZ ≤Z subtractInt n i ∧
   subtractInt n next <Z subtractInt n i) ∧
  (zeroZ ≤Z next ∧ next <Z n) ∧
  (zeroZ <Z
     belowCount (elts current) j value (addInt next oneZ) n ∧
   zeroZ ≤Z j ∧ j <Z c) ∧
  value <Z elts current next j

AboveColumnProgress :
  Matrix → Int → Int → Set
AboveColumnProgress current n c =
  (value i j : Int) →
  (zeroZ ≤Z i ∧ i <Z n) ∧
  (zeroZ <Z aboveCount (elts current) j value zeroZ i ∧
   zeroZ ≤Z j ∧ j <Z c) ∧
  elts current i j ≤Z value →
  let previous = subtractInt i oneZ
  in
  (zeroZ ≤Z i ∧ previous <Z i) ∧
  (zeroZ ≤Z previous ∧ previous <Z n) ∧
  (zeroZ <Z aboveCount (elts current) j value zeroZ previous ∧
   zeroZ ≤Z j ∧ j <Z c) ∧
  elts current previous j ≤Z value

ColumnProgress : Matrix → Int → Int → Set
ColumnProgress current n c =
  BelowColumnProgress current n c ∧
  AboveColumnProgress current n c

AfterColumnSort :
  Matrix → Matrix →
  (Int → Int) → (Int → Int) →
  Int → Int → Int → Int → Int → Set
AfterColumnSort original current newz newo kd n c l ind =
  ColumnProgress current n c ∧
  Zones newz newo kd current n c ∧
  zeroZ <Z kd ∧
  PowerBounds kd (addInt ind oneZ) n ∧
  (l <Z addInt ind oneZ → SnakeRows current n c) ∧
  PreservesOccurrences original current n c

AfterNzo :
  Matrix → Matrix →
  (Int → Int) → (Int → Int) →
  (Int → Pair Int Int) →
  Int → Int → Int → Int → Int → Set
AfterNzo original row-sorted zeros ones nzo kd n c l ind =
  (value : Int) →
  let bounds = nzo value
  in
  NzoProperty (elts row-sorted) value kd n c bounds →
  ((result : Int) →
    result ≡ fst bounds →
    result ≡ fst (nzo value)) ∧
  ((newz : Int → Int) →
    ((value1 : Int) → newz value1 ≡ fst (nzo value1)) →
    (value1 : Int) →
    let bounds1 = nzo value1
    in
    NzoProperty (elts row-sorted) value1 kd n c bounds1 →
    ((result : Int) →
      result ≡ snd bounds1 →
      result ≡ snd (nzo value1)) ∧
    ((newo : Int → Int) →
      ((value2 : Int) → newo value2 ≡ snd (nzo value2)) →
      (ind ≡ l →
        Zones zeros ones oneZ row-sorted n c) ∧
      ((ind ≡ l → CrossRows row-sorted n c) →
        (column-sorted : Matrix) →
        Dimensions column-sorted row-sorted →
        ColumnPermuted column-sorted row-sorted ∧
        ColumnSorted
          column-sorted
          (rows column-sorted)
          (columns column-sorted) →
        AfterColumnSort
          original column-sorted newz newo kd n c l ind)))

SelectionVC :
  Matrix → Matrix →
  (Int → Int) → (Int → Int) →
  Int → Int → Int → Int → Int → Set
SelectionVC original row-sorted zeros ones k n c l ind =
  let e = elts row-sorted
      kd = divTwo (addInt k oneZ)
  in
  twoZ ≠ zeroZ ∧
  (((value : Int) →
    let z = zeros value
        o = ones value
    in
    SelectionInitial e value z o n c ∧
    SelectionLoop e value z o kd n c) ∧
   ((nzo : Int → Pair Int Int) →
    ((value : Int) →
      NzoProperty e value kd n c (nzo value)) →
    AfterNzo
      original row-sorted zeros ones nzo kd n c l ind))

OuterInvariant :
  Matrix → Matrix →
  (Int → Int) → (Int → Int) →
  Int → Int → Int → Int → Int → Set
OuterInvariant original current zeros ones k n c l ind =
  (zeroZ ≤Z ind ∧ ind ≤Z l) ∧
  Zones zeros ones k current n c ∧
  zeroZ <Z k ∧
  PowerBounds k ind n ∧
  (l <Z ind → SnakeRows current n c) ∧
  PreservesOccurrences original current n c

RowRound :
  Matrix → Matrix →
  (Int → Int) → (Int → Int) →
  Int → Int → Int → Int → Int → Set
RowRound original current zeros ones k n c l ind =
  (row-sorted : Matrix) →
  Dimensions row-sorted current →
  RowPermuted row-sorted current ∧
  SnakeRows
    row-sorted (rows row-sorted) (columns row-sorted) →
  SelectionVC
    original row-sorted zeros ones k n c l ind

OuterExitInvariant :
  Matrix → Matrix →
  (Int → Int) → (Int → Int) →
  Int → Int → Int → Int → Set
OuterExitInvariant original current zeros ones k n c l =
  Zones zeros ones k current n c ∧
  zeroZ <Z k ∧
  PowerBounds k (addInt l oneZ) n ∧
  (l <Z addInt l oneZ → SnakeRows current n c) ∧
  PreservesOccurrences original current n c

OuterExitPost :
  Matrix → Matrix →
  (Int → Int) → (Int → Int) →
  Int → Int → Int → Int → Set
OuterExitPost original current zeros ones k n c l =
  OuterExitInvariant original current zeros ones k n c l →
  Zones zeros ones oneZ current n c ∧
  (CrossRows current n c →
    FinalMatrixPost original current)

OuterBody :
  Matrix →
  (Int → Int) → (Int → Int) →
  Int → Matrix → Int → Int → Int → Set
OuterBody original zeros ones k current n c l =
  (ind : Int) →
  OuterInvariant original current zeros ones k n c l ind →
  RowRound original current zeros ones k n c l ind

InitialOuterInvariant : Matrix → Int → Int → Int → Set
InitialOuterInvariant original n c l =
  ExtremeZones n original n c ∧
  zeroZ <Z n ∧
  PowerBounds n zeroZ n ∧
  (l <Z zeroZ → SnakeRows original n c)

WidthOneImpliesCross : Matrix → Int → Int → Set
WidthOneImpliesCross original n c =
  (ones zeros : Int → Int) (current : Matrix) →
  Dimensions current original →
  Zones zeros ones oneZ current n c →
  CrossRows current n c

NegativeOuterBranch : Matrix → Int → Int → Set
NegativeOuterBranch original n c =
  ExtremeZones oneZ original n c ∧
  (CrossRows original n c →
    CrossRows original (rows original) (columns original) ∧
    SnakeRows original (rows original) (columns original))

OuterLoopVC : Matrix → Int → Int → Int → Set
OuterLoopVC original n c l =
  WidthOneImpliesCross original n c ∧
  ((zeroZ ≤Z addInt l oneZ →
    InitialOuterInvariant original n c l ∧
    ((ones zeros : Int → Int) (k : Int) (current : Matrix) →
      Dimensions current original →
      OuterBody original zeros ones k current n c l ∧
      OuterExitPost original current zeros ones k n c l)) ∧
   (addInt l oneZ <Z zeroZ →
    NegativeOuterBranch original n c))

LogInvariant : Int → Int → Int → Set
LogInvariant p l n =
  (zeroZ ≤Z l ∧ zeroZ ≤Z p) ∧
  (l ≠ zeroZ →
    powerInt twoZ (subtractInt l oneZ) ≤Z n) ∧
  multiplyInt p (powerInt twoZ l) <Z n ∧
  n ≤Z
    multiplyInt (powerInt twoZ l) (addInt p oneZ)

LogStep : Int → Int → Int → Set
LogStep p l n =
  twoZ ≠ zeroZ ∧
  (zeroZ ≤Z p ∧ divTwo p <Z p) ∧
  (zeroZ ≤Z addInt l oneZ ∧ zeroZ ≤Z divTwo p) ∧
  (addInt l oneZ ≠ zeroZ →
    powerInt twoZ
      (subtractInt (addInt l oneZ) oneZ) ≤Z n) ∧
  multiplyInt
    (divTwo p)
    (powerInt twoZ (addInt l oneZ)) <Z n ∧
  n ≤Z
    multiplyInt
      (powerInt twoZ (addInt l oneZ))
      (addInt (divTwo p) oneZ)

LogLoopVC : Matrix → Int → Int → Set
LogLoopVC original n c =
  (p l : Int) →
  LogInvariant p l n →
  ifSet (notBool (intEqual p zeroZ))
    (LogStep p l n)
    (OuterLoopVC original n c l)

NonemptyMatrixVC : Matrix → Int → Int → Set
NonemptyMatrixVC original n c =
  let last-row = subtractInt n oneZ
  in
  ((zeroZ ≤Z zeroZ ∧ zeroZ ≤Z last-row) ∧
   multiplyInt last-row (powerInt twoZ zeroZ) <Z n ∧
   n ≤Z
     multiplyInt
       (powerInt twoZ zeroZ)
       (addInt last-row oneZ)) ∧
  LogLoopVC original n c

EmptyMatrixVC : Matrix → Set
EmptyMatrixVC original =
  CrossRows original (rows original) (columns original) ∧
  SnakeRows original (rows original) (columns original)

ShearSortVC : Matrix → Set
ShearSortVC original =
  let n = rows original
      c = columns original
  in
  ifSet (notBool (intEqual n zeroZ))
    (NonemptyMatrixVC original n c)
    (EmptyMatrixVC original)

shear-sort-vc : Set
shear-sort-vc = (original : Matrix) → ShearSortVC original
