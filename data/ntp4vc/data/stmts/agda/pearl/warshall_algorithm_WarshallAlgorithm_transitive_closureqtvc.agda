-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/warshall_algorithm_WarshallAlgorithm_transitive_closureqtvc: the
-- verification condition for Warshall's Boolean-matrix transitive-closure
-- algorithm and its three nested loop invariants. This file contains no proof.

{-# OPTIONS --safe #-}

module warshall_algorithm_WarshallAlgorithm_transitive_closureqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_
infix 2 _↔_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

ifValue : {A : Set} → Bool → A → A → A
ifValue true when-true when-false = when-true
ifValue false when-true when-false = when-false

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

andBool : Bool → Bool → Bool
andBool true value = value
andBool false value = false

orBool : Bool → Bool → Bool
orBool true value = true
orBool false value = value

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

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

record Matrix : Set where
  constructor matrix
  field
    rows                : Int
    columns             : Int
    elts                : Int → Int → Bool
    rows-nonnegative    : zeroZ ≤Z rows
    columns-nonnegative : zeroZ ≤Z columns

open Matrix

Bounded : Int → Int → Set
Bounded index upper =
  (zeroZ ≤Z index) ∧ (index <Z upper)

ValidIndex : Matrix → Int → Int → Set
ValidIndex m row column =
  Bounded row (rows m) ∧
  Bounded column (columns m)

SameDimensions : Matrix → Matrix → Set
SameDimensions first-matrix second-matrix =
  rows first-matrix ≡ rows second-matrix ∧
  columns first-matrix ≡ columns second-matrix

data Path : Matrix → Int → Int → Int → Set where
  path-empty :
    (m : Matrix) →
    (i j k : Int) →
    elts m i j ≡ true →
    Path m i j k

  path-cons :
    (x k : Int) →
    (m : Matrix) →
    (i j : Int) →
    zeroZ ≤Z x →
    x <Z k →
    Path m i x k →
    Path m x j k →
    Path m i j k

ClosureInvariant :
  Matrix →
  Matrix →
  Int →
  Int →
  Set
ClosureInvariant original state n k =
  (x y : Int) →
  Bounded x n →
  Bounded y n →
  (elts state x y ≡ true) ↔ Path original x y k

RowInvariant :
  Matrix →
  Matrix →
  Int →
  Int →
  Int →
  Set
RowInvariant original state n boundary k =
  (x y : Int) →
  Bounded x n →
  Bounded y n →
  (elts state x y ≡ true) ↔
  IfSet
    (intLess x boundary)
    (Path original x y (addInt k oneZ))
    (Path original x y k)

beforeCell : Int → Int → Int → Int → Bool
beforeCell x y i j =
  orBool
    (intLess x i)
    (andBool (intEqual x i) (intLess y j))

CellInvariant :
  Matrix →
  Matrix →
  Int →
  Int →
  Int →
  Int →
  Set
CellInvariant original state n i j k =
  (x y : Int) →
  Bounded x n →
  Bounded y n →
  (elts state x y ≡ true) ↔
  IfSet
    (beforeCell x y i j)
    (Path original x y (addInt k oneZ))
    (Path original x y k)

updateElts :
  (Int → Int → Bool) →
  Int →
  Int →
  Bool →
  Int →
  Int →
  Bool
updateElts old row column value query-row query-column =
  ifValue
    (intEqual query-row row)
    (ifValue
      (intEqual query-column column)
      value
      (old query-row query-column))
    (old query-row query-column)

ElementsAfterUpdate :
  Matrix →
  Matrix →
  Int →
  Int →
  Bool →
  Set
ElementsAfterUpdate old new row column value =
  (query-row query-column : Int) →
  elts new query-row query-column ≡
  updateElts (elts old) row column value query-row query-column

nextEntry : Bool → Bool → Bool → Bool
nextEntry old through-left through-right =
  ifValue old true (ifValue through-left through-right false)

CellBody :
  Matrix →
  Int →
  Int →
  Int →
  Int →
  Matrix →
  Set
CellBody original n k i j state =
  ValidIndex state i j ∧
  let old = elts state i j
  in
  (Not (old ≡ true) →
    ValidIndex state i k ∧
    (elts state i k ≡ true → ValidIndex state k j))
  ∧
  ((new-value : Bool) →
    new-value ≡
      nextEntry old (elts state i k) (elts state k j) →
    ValidIndex state i j ∧
    ((new-state : Matrix) →
      SameDimensions new-state state →
      ElementsAfterUpdate state new-state i j new-value →
      CellInvariant
        original
        new-state
        n
        i
        (addInt j oneZ)
        k))

ColumnLoopVC :
  Matrix →
  Int →
  Int →
  Int →
  Matrix →
  Set
ColumnLoopVC original n k i initial-state =
  let upper = subtractInt n oneZ
      after-last = addInt upper oneZ
  in
  (zeroZ ≤Z after-last →
    CellInvariant original initial-state n i zeroZ k ∧
    ((state : Matrix) →
      SameDimensions state initial-state →
      (((j : Int) →
        ((zeroZ ≤Z j ∧ j ≤Z upper) ∧
         CellInvariant original state n i j k) →
        CellBody original n k i j state)
       ∧
       (CellInvariant original state n i after-last k →
        RowInvariant
          original
          state
          n
          (addInt i oneZ)
          k))))
  ∧
  (after-last <Z zeroZ →
    RowInvariant
      original
      initial-state
      n
      (addInt i oneZ)
      k)

RowLoopVC :
  Matrix →
  Int →
  Int →
  Matrix →
  Set
RowLoopVC original n k initial-state =
  let upper = subtractInt n oneZ
      after-last = addInt upper oneZ
  in
  (zeroZ ≤Z after-last →
    RowInvariant original initial-state n zeroZ k ∧
    ((state : Matrix) →
      SameDimensions state initial-state →
      (((i : Int) →
        ((zeroZ ≤Z i ∧ i ≤Z upper) ∧
         RowInvariant original state n i k) →
        ColumnLoopVC original n k i state)
       ∧
       (RowInvariant original state n after-last k →
        ClosureInvariant
          original
          state
          n
          (addInt k oneZ)))))
  ∧
  (after-last <Z zeroZ →
    ClosureInvariant
      original
      initial-state
      n
      (addInt k oneZ))

WarshallLoopVC : Matrix → Matrix → Set
WarshallLoopVC original initial-state =
  let n = rows original
      upper = subtractInt n oneZ
      after-last = addInt upper oneZ
  in
  (zeroZ ≤Z after-last →
    ClosureInvariant original initial-state n zeroZ ∧
    ((state : Matrix) →
      SameDimensions state initial-state →
      (((k : Int) →
        ((zeroZ ≤Z k ∧ k ≤Z upper) ∧
         ClosureInvariant original state n k) →
        RowLoopVC original n k state)
       ∧
       (ClosureInvariant original state n after-last →
        let final-n = rows original
        in ClosureInvariant
          original
          state
          final-n
          final-n))))
  ∧
  (after-last <Z zeroZ →
    let final-n = rows original
    in ClosureInvariant
      original
      initial-state
      final-n
      final-n)

transitive-closure'vc : Set
transitive-closure'vc =
  (m t : Matrix) →
  rows m ≡ columns m →
  rows t ≡ rows m →
  columns t ≡ columns m →
  ((r : Int) →
    Bounded r (rows t) →
    (c : Int) →
    Bounded c (columns t) →
    elts t r c ≡ elts m r c) →
  WarshallLoopVC m t
