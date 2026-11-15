-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/linked_list_rev_Termination_list_reversalqtvc: the linked-list
-- reversal termination verification condition, including finite-memory,
-- marker-count, invariant, and pointer-update obligations. This file contains no proof.

{-# OPTIONS --safe #-}

module linked_list_rev_Termination_list_reversalqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_ _≢_
infixr 3 _∧_
infixr 2 _∨_
infix 2 _↔_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

_≢_ : {A : Set} → A → A → Set
x ≢ y = Not (x ≡ y)

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : Not P → Dec P

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

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

natToInt : Nat → Int
natToInt = pos

zeroZ oneZ minusOneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
minusOneZ = negsuc zero

countFrom : (Int → Bool) → Int → Nat → Nat
countFrom predicate start zero = zero
countFrom predicate start (suc count) with predicate start
... | true = suc (countFrom predicate (addInt start oneZ) count)
... | false = countFrom predicate (addInt start oneZ) count

numOf : (Int → Bool) → Int → Int → Int
numOf predicate lower upper =
  natToInt
    (countFrom predicate lower (toNat (subtractInt upper lower)))

record LinkedListModel : Set₁ where
  field
    Loc            : Set
    null           : Loc
    excludedMiddle : (P : Set) → P ∨ Not P

open LinkedListModel

decide :
  (model : LinkedListModel) →
  (P : Set) →
  Dec P
decide model P with excludedMiddle model P
... | left proof = yes proof
... | right refutation = no refutation

update :
  (model : LinkedListModel) →
  {A : Set} →
  (Loc model → A) →
  Loc model →
  A →
  Loc model →
  A
update model old key value query with decide model (query ≡ key)
... | yes _ = value
... | no _ = old query

Range :
  Int →
  Int →
  Set
Range i n = zeroZ ≤Z i ∧ i <Z n

ValidCells :
  (model : LinkedListModel) →
  (Int → Loc model) →
  Int →
  Set
ValidCells model s n =
  ((i : Int) →
    Range i n →
    s i ≢ null model)
  ∧
  ((i j : Int) →
    Range i n →
    Range j n →
    i ≢ j →
    s i ≢ s j)

InsideMemory :
  (model : LinkedListModel) →
  (Int → Loc model) →
  Int →
  Loc model →
  Set
InsideMemory model s n l =
  (l ≡ null model)
  ∨
  Σ Int (λ i → Range i n ∧ l ≡ s i)

FiniteMemory :
  (model : LinkedListModel) →
  (Loc model → Loc model) →
  (Int → Loc model) →
  Int →
  Set
FiniteMemory model next s n =
  (i : Int) →
  Range i n →
  InsideMemory model s n (next (s i))

fc :
  (model : LinkedListModel) →
  (Int → Loc model) →
  (Loc model → Int) →
  Int →
  Bool
fc model s idx i = intLess zeroZ (idx (s i))

seen :
  (model : LinkedListModel) →
  (Int → Loc model) →
  (Loc model → Int) →
  Int →
  Int →
  Int
seen model s idx lower upper =
  numOf (fc model s idx) lower upper

initialMarker :
  (model : LinkedListModel) →
  Loc model →
  Int
initialMarker model p with decide model (p ≡ null model)
... | yes _ = zeroZ
... | no _ = minusOneZ

MarkerBounds :
  (model : LinkedListModel) →
  (Int → Loc model) →
  Int →
  (Loc model → Int) →
  Int →
  Set
MarkerBounds model s n idx upper =
  (i : Int) →
  Range i n →
  minusOneZ ≤Z idx (s i)
  ∧ idx (s i) ≤Z upper

ZeroExactlyNull :
  (model : LinkedListModel) →
  (Loc model → Int) →
  Set
ZeroExactlyNull model idx =
  (p : Loc model) →
  (idx p ≡ zeroZ) ↔ (p ≡ null model)

ChainCondition :
  (model : LinkedListModel) →
  (Int → Loc model) →
  Int →
  (Loc model → Loc model) →
  (Loc model → Int) →
  Loc model →
  Loc model →
  Int →
  Set
ChainCondition model s n next idx r l upper =
  IfSet
    (intEqual (idx l) minusOneZ)
    (idx r ≡ upper
     ∧
     ((i : Int) →
       Range i n →
       zeroZ <Z idx (s i) →
       idx (next (s i)) ≡ subtractInt (idx (s i)) oneZ))
    ((i : Int) →
      Range i n →
      (zeroZ <Z idx (s i) ∧ idx (s i) ≤Z idx l) →
      idx (next (s i)) ≡ subtractInt (idx (s i)) oneZ)

LoopInvariant :
  (model : LinkedListModel) →
  (Int → Loc model) →
  Int →
  (Loc model → Loc model) →
  (Loc model → Int) →
  Loc model →
  Loc model →
  Set
LoopInvariant model s n next idx r l =
  InsideMemory model s n l
  ∧ InsideMemory model s n r
  ∧ FiniteMemory model next s n
  ∧ zeroZ ≤Z seen model s idx zeroZ n
  ∧ MarkerBounds model s n idx (seen model s idx zeroZ n)
  ∧ ZeroExactlyNull model idx
  ∧ ChainCondition
      model s n next idx r l
      (seen model s idx zeroZ n)

InitialState :
  (model : LinkedListModel) →
  (Int → Loc model) →
  Int →
  Loc model →
  (Loc model → Loc model) →
  Set
InitialState model s n l mem₁ =
  let marker = initialMarker model
      count = seen model s marker zeroZ n
  in
  InsideMemory model s n l
  ∧ InsideMemory model s n (null model)
  ∧ FiniteMemory model mem₁ s n
  ∧ (zeroZ ≡ count ∧ zeroZ ≤Z count)
  ∧ MarkerBounds model s n marker zeroZ
  ∧ ZeroExactlyNull model marker
  ∧ ChainCondition model s n mem₁ marker (null model) l zeroZ

UpdatedState :
  (model : LinkedListModel) →
  (Int → Loc model) →
  Int →
  (Loc model → Int) →
  Loc model →
  Loc model →
  (Loc model → Loc model) →
  Set
UpdatedState model s n idx r l₁ mem₃ =
  let count = seen model s idx zeroZ n
      nextCount = addInt count oneZ
      updatedIdx = update model idx l₁ nextCount
      updatedMem = update model mem₃ l₁ r
      nextLocation = mem₃ l₁
  in
  l₁ ≢ null model
  ∧ l₁ ≢ null model
  ∧
    ((zeroZ ≤Z subtractInt n count
      ∧ subtractInt n nextCount <Z subtractInt n count)
     ∨
     (subtractInt n count ≡ subtractInt n nextCount
      ∧ zeroZ ≤Z addInt oneZ (idx l₁)
      ∧ addInt oneZ (updatedIdx nextLocation) <Z
          addInt oneZ (idx l₁)))
  ∧ InsideMemory model s n nextLocation
  ∧ InsideMemory model s n l₁
  ∧ FiniteMemory model updatedMem s n
  ∧ (nextCount ≡ seen model s updatedIdx zeroZ n
     ∧ zeroZ ≤Z seen model s updatedIdx zeroZ n)
  ∧ MarkerBounds model s n updatedIdx nextCount
  ∧ ZeroExactlyNull model updatedIdx
  ∧ ChainCondition
      model s n updatedMem updatedIdx l₁ nextLocation nextCount

FirstVisitConclusion :
  (model : LinkedListModel) →
  (Int → Loc model) →
  Int →
  (Loc model → Int) →
  Loc model →
  Loc model →
  (Loc model → Loc model) →
  Set
FirstVisitConclusion model s n idx r l₁ mem₃ =
  let count = seen model s idx zeroZ n
      nextCount = addInt count oneZ
      expectedCount = addInt oneZ count
      updatedIdx = update model idx l₁ nextCount
  in
  (ValidCells model s n
   ∧ InsideMemory model s n l₁
   ∧ l₁ ≢ null model
   ∧ idx l₁ ≡ minusOneZ
  ∧ zeroZ ≤Z count)
  ∧
  (seen model s updatedIdx zeroZ n ≡ expectedCount →
   UpdatedState model s n idx r l₁ mem₃)

AlreadySeenConclusion :
  (model : LinkedListModel) →
  (Int → Loc model) →
  Int →
  (Loc model → Int) →
  Loc model →
  Loc model →
  (Loc model → Loc model) →
  Set
AlreadySeenConclusion model s n idx r l₁ mem₃ =
  let count = seen model s idx zeroZ n
      nextLocation = mem₃ l₁
      updatedMem = update model mem₃ l₁ r
  in
  l₁ ≢ null model
  ∧ l₁ ≢ null model
  ∧
    ((zeroZ ≤Z subtractInt n count
      ∧ subtractInt n count <Z subtractInt n count)
     ∨
     (zeroZ ≤Z addInt oneZ (idx l₁)
      ∧ addInt oneZ (idx nextLocation) <Z
          addInt oneZ (idx l₁)))
  ∧ LoopInvariant model s n updatedMem idx l₁ nextLocation

LoopStep :
  (model : LinkedListModel) →
  (Int → Loc model) →
  Int →
  Set
LoopStep model s n =
  (idx : Loc model → Int) →
  (r l₁ : Loc model) →
  (mem₃ : Loc model → Loc model) →
  LoopInvariant model s n mem₃ idx r l₁ →
  l₁ ≢ null model →
  IfSet
    (intEqual (idx l₁) minusOneZ)
    (FirstVisitConclusion model s n idx r l₁ mem₃)
    (AlreadySeenConclusion model s n idx r l₁ mem₃)

list-reversal'vc : Set₁
list-reversal'vc =
  (model : LinkedListModel) →
  (mem₁ : Loc model → Loc model) →
  (s : Int → Loc model) →
  (n : Int) →
  (l : Loc model) →
  (zeroZ ≤Z n
   ∧ ValidCells model s n
   ∧ FiniteMemory model mem₁ s n
   ∧ InsideMemory model s n l)
  →
  InitialState model s n l mem₁
  ∧ LoopStep model s n
