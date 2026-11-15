-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/avl/priority_queue_PQueue_selected_partqtvc: a priority-queue
-- verification condition selecting a pivot-relative split from the aggregate
-- minima of two sequences. This file contains no proof.

{-# OPTIONS --safe #-}

module priority_queue_PQueue_selected_partqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)

infix 4 _≤Z_ _<Z_ _≢_
infix 3 _↔_
infixr 3 _∧_
infixr 2 _∨_

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

data Dec (A : Set) : Set where
  yes : A → Dec A
  no  : (A → ⊥) → Dec A

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

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

natToInt : Nat → Int
natToInt = pos

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc _) = zero

zeroZ : Int
zeroZ = pos zero

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

append : {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) = nthDefault default n xs

record Split (A : Set) : Set where
  constructor split
  field
    leftPart   : List A
    middlePart : Maybe A
    rightPart  : List A

open Split

optionToList : {A : Set} → Maybe A → List A
optionToList nothing = []
optionToList (just x) = x ∷ []

rebuild : {A : Set} → Split A → List A
rebuild parts =
  append
    (leftPart parts)
    (append (optionToList (middlePart parts)) (rightPart parts))

leftExtend : {A : Set} → List A → A → Split A → Split A
leftExtend prefix datum parts =
  split
    (append prefix (datum ∷ leftPart parts))
    (middlePart parts)
    (rightPart parts)

rightExtend : {A : Set} → Split A → A → List A → Split A
rightExtend parts datum suffix =
  split
    (leftPart parts)
    (middlePart parts)
    (append (rightPart parts) (datum ∷ suffix))

data PartBase (A : Set) : Set where
  Left  : A → PartBase A
  Right : A → PartBase A
  Here  : PartBase A

Strict :
  {Key : Set} → (Key → Key → Set) → Key → Key → Set
Strict leKey x y = leKey x y ∧ (leKey y x → ⊥)

module PriorityQueueTheory
  (balancing : Nat)
  (balancingPositive : zeroZ <Z natToInt balancing)
  (Key : Set)
  (keyDefault : Key)
  (leKey : Key → Key → Set)
  (leRefl : (x : Key) → leKey x x)
  (leTrans :
    (x y z : Key) → leKey x y → leKey y z → leKey x z)
  (leTotal : (x y : Key) → leKey x y ∨ leKey y x)
  (Element : Set → Set)
  (elementDefault : {A : Set} → A → Element A)
  (key : {A : Set} → A → Element A → Key)
  (strictDec : (x y : Key) → Dec (Strict leKey x y))
  where

  infix 4 _≤K_ _<K_ _≈K_

  _≤K_ : Key → Key → Set
  _≤K_ = leKey

  _<K_ : Key → Key → Set
  _<K_ = Strict leKey

  _≈K_ : Key → Key → Set
  x ≈K y = (x ≤K y) ∧ (y ≤K x)

  op : Maybe Key → Maybe Key → Maybe Key
  op nothing y = y
  op x@(just _) nothing = x
  op x@(just a) y@(just b) with strictDec b a
  ... | yes _ = y
  ... | no _ = x

  aggregate :
    {A : Set} → A → (A → Maybe Key) → List A → Maybe Key
  aggregate defaultA f [] = nothing
  aggregate defaultA f (x ∷ xs) =
    op (f x) (aggregate defaultA f xs)

  measureClosure :
    {A : Set} → A → Element A → Maybe Key
  measureClosure defaultA datum = just (key defaultA datum)

  aggregateMeasure :
    {A : Set} → A → List (Element A) → Maybe Key
  aggregateMeasure defaultA values =
    aggregate
      (elementDefault defaultA)
      (measureClosure defaultA)
      values

  selectionPossible :
    {X Y : Set} → X → List Y → Set
  selectionPossible selector values =
    natToInt (length values) ≢ zeroZ

  lowerBound :
    {A : Set} → A → Key → List (Element A) → Set
  lowerBound defaultA lower values =
    (i : Int) →
    (zeroZ ≤Z i ∧ i <Z natToInt (length values)) →
    lower ≤K
      key defaultA
        (nthDefault
          (elementDefault defaultA)
          (intToNat i)
          values)

  lowerBoundStrict :
    {A : Set} → A → Key → List (Element A) → Set
  lowerBoundStrict defaultA lower values =
    (i : Int) →
    (zeroZ ≤Z i ∧ i <Z natToInt (length values)) →
    lower <K
      key defaultA
        (nthDefault
          (elementDefault defaultA)
          (intToNat i)
          values)

  selected :
    {A : Set} → A → ⊤ → Split (Element A) → Set
  selected defaultA selector parts with middlePart parts
  ... | nothing = ⊥
  ... | just datum =
    lowerBound defaultA (key defaultA datum) (rightPart parts) ∧
    lowerBoundStrict defaultA (key defaultA datum) (leftPart parts)

  Comparison : Int → Key → Key → Set
  Comparison comparison leftKey rightKey =
    ((zeroZ <Z comparison) ↔ (leftKey <K rightKey)) ∧
    ((comparison <Z zeroZ) ↔ (rightKey <K leftKey)) ∧
    ((comparison ≡ zeroZ) ↔ (rightKey ≈K leftKey))

  noneRightResult : PartBase ⊤ → Key → Key → Set
  noneRightResult result leftKey pivotKey =
    Σ Int λ comparison →
      Comparison comparison leftKey pivotKey ∧
      IfSet
        (intLess comparison zeroZ)
        (result ≡ Here)
        (result ≡ Left tt)

  rightNoneResult : PartBase ⊤ → Key → Key → Set
  rightNoneResult result rightKey pivotKey =
    Σ Int λ comparison →
      Comparison comparison rightKey pivotKey ∧
      IfSet
        (intLessOrEqual comparison zeroZ)
        (result ≡ Here)
        (result ≡ Right tt)

  bothLeftResult : PartBase ⊤ → Key → Key → Set
  bothLeftResult result pivotKey leftKey =
    Σ Int λ comparison →
      Comparison comparison pivotKey leftKey ∧
      IfSet
        (intLessOrEqual comparison zeroZ)
        (result ≡ Left tt)
        (result ≡ Here)

  bothRightResult : PartBase ⊤ → Key → Key → Set
  bothRightResult result rightKey leftKey =
    Σ Int λ comparison →
      Comparison comparison rightKey leftKey ∧
      IfSet
        (intLessOrEqual comparison zeroZ)
        (result ≡ Left tt)
        (result ≡ Right tt)

  bothResult : PartBase ⊤ → Key → Key → Key → Set
  bothResult result rightKey leftKey pivotKey =
    Σ Int λ comparison →
      Comparison comparison rightKey pivotKey ∧
      IfSet
        (intLessOrEqual comparison zeroZ)
        (bothLeftResult result pivotKey leftKey)
        (bothRightResult result rightKey leftKey)

  operationalResult :
    {A : Set} → A → Element A →
    List (Element A) → List (Element A) →
    PartBase ⊤ → Set
  operationalResult defaultA datum rightValues leftValues result
    with aggregateMeasure defaultA rightValues
       | aggregateMeasure defaultA leftValues
  ... | nothing | nothing = result ≡ Here
  ... | nothing | just leftKey =
        noneRightResult
          result leftKey (key defaultA datum)
  ... | just rightKey | nothing =
        rightNoneResult
          result rightKey (key defaultA datum)
  ... | just rightKey | just leftKey =
        bothResult
          result rightKey leftKey (key defaultA datum)

  initialMatch :
    {A : Set} → A →
    List (Element A) → List (Element A) → Set
  initialMatch defaultA rightValues leftValues
    with aggregateMeasure defaultA rightValues
       | aggregateMeasure defaultA leftValues
  ... | nothing | nothing = ⊤
  ... | nothing | just _ = ⊤
  ... | just _ | nothing = ⊤
  ... | just _ | just _ = ⊤

  resultContract :
    {A : Set} → A → Element A →
    List (Element A) → List (Element A) →
    PartBase ⊤ → Set
  resultContract defaultA datum rightValues leftValues Here =
    selected defaultA tt
      (split leftValues (just datum) rightValues)
  resultContract defaultA datum rightValues leftValues
    (Left leftSelector) =
      selectionPossible leftSelector leftValues ∧
      ((parts : Split (Element _)) →
        (selected defaultA leftSelector parts ∧
         rebuild parts ≡ leftValues) →
        selected defaultA tt
          (rightExtend parts datum rightValues))
  resultContract defaultA datum rightValues leftValues
    (Right rightSelector) =
      selectionPossible rightSelector rightValues ∧
      ((parts : Split (Element _)) →
        (selected defaultA rightSelector parts ∧
         rebuild parts ≡ rightValues) →
        selected defaultA tt
          (leftExtend leftValues datum parts))

  module WithOptionMonoidLaws
    (opAssoc :
      (a b c : Maybe Key) →
      op a (op b c) ≡ op (op a b) c)
    (opNeutral :
      (x : Maybe Key) →
      (op x nothing ≡ x) ∧ (x ≡ op nothing x))
    where

    selected-part'vc : Set₁
    selected-part'vc =
      (A : Set) →
      (defaultA : A) →
      (datum : Element A) →
      (rightValues : List (Element A)) →
      (leftValues : List (Element A)) →
      initialMatch defaultA rightValues leftValues ∧
      ((result : PartBase ⊤) →
        operationalResult
          defaultA datum rightValues leftValues result →
        resultContract
          defaultA datum rightValues leftValues result)
