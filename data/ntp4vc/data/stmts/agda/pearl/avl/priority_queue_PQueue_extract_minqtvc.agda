-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/avl/priority_queue_PQueue_extract_minqtvc: a priority-queue minimum
-- extraction verification condition for sequence splitting and bag updates.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module priority_queue_PQueue_extract_minqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_ _≢_
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

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

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

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

negateInt : Int → Int
negateInt (pos n) = negative n
negateInt (negsuc n) = pos (suc n)

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

addInt : Int → Int → Int
addInt (pos m) (pos n) = pos (m + n)
addInt (pos m) (negsuc n) = difference m (suc n)
addInt (negsuc m) (pos n) = difference n (suc m)
addInt (negsuc m) (negsuc n) = negsuc (suc (m + n))

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

natToInt : Nat → Int
natToInt = pos

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc _) = zero

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

maxInt : Int → Int → Int
maxInt x y with intLess x y
... | true = y
... | false = x

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

append : {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

take : {A : Set} → Nat → List A → List A
take zero xs = []
take (suc n) [] = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : {A : Set} → Nat → List A → List A
drop zero xs = xs
drop (suc n) [] = []
drop (suc n) (_ ∷ xs) = drop n xs

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

record Model (X : Set) : Set where
  constructor model
  field
    seq : List X
    hgt : Int

open Model

data Tree (Key : Set) (Element : Set → Set) (A : Set) : Set where
  Empty : Tree Key Element A
  Node  :
    Tree Key Element A →
    Element A →
    Tree Key Element A →
    Nat →
    Maybe Key →
    Tree Key Element A

nodeModel : {A : Set} → List A → A → List A → List A
nodeModel leftValues datum rightValues =
  append leftValues (datum ∷ rightValues)

seqModel :
  {Key : Set} {Element : Set → Set} {A : Set} →
  Tree Key Element A → List (Element A)
seqModel Empty = []
seqModel (Node leftTree datum rightTree _ _) =
  nodeModel (seqModel leftTree) datum (seqModel rightTree)

realHeight :
  {Key : Set} {Element : Set → Set} {A : Set} →
  Tree Key Element A → Int
realHeight Empty = zeroZ
realHeight (Node leftTree _ rightTree _ _) =
  addInt oneZ (maxInt (realHeight leftTree) (realHeight rightTree))

record QueueSummary (Element : Set → Set) (A : Set) : Set where
  constructor queueSummary
  field
    bag     : Element A → Int
    minimum : Element A
    card    : Int

open QueueSummary

module PriorityQueueTheory
  (Key : Set)
  (leKey : Key → Key → Set)
  (leRefl : (x : Key) → leKey x x)
  (leTrans :
    (x y z : Key) → leKey x y → leKey y z → leKey x z)
  (leTotal : (x y : Key) → leKey x y ∨ leKey y x)
  (Element : Set → Set)
  (elementDefault : {A : Set} → A → Element A)
  (key : {A : Set} → A → Element A → Key)
  (op : Maybe Key → Maybe Key → Maybe Key)
  (opNothingLeft : (x : Maybe Key) → op nothing x ≡ x)
  (opNothingRight : (x : Maybe Key) → op x nothing ≡ x)
  (opChooseRight :
    (a b : Key) →
    (leKey b a ∧ (leKey a b → ⊥)) →
    op (just a) (just b) ≡ just b)
  (opKeepLeft :
    (a b : Key) →
    ((leKey b a ∧ (leKey a b → ⊥)) → ⊥) →
    op (just a) (just b) ≡ just a)
  (opAssoc :
    (a b c : Maybe Key) → op a (op b c) ≡ op (op a b) c)
  (opNeutral :
    (x : Maybe Key) →
    (op x nothing ≡ x) ∧ (x ≡ op nothing x))
  where

  infix 4 _≤K_ _<K_

  _≤K_ : Key → Key → Set
  _≤K_ = leKey

  _<K_ : Key → Key → Set
  x <K y = (x ≤K y) ∧ (y ≤K x → ⊥)

  aggregate :
    {A : Set} → A → (A → Maybe Key) → List A → Maybe Key
  aggregate defaultA f [] = nothing
  aggregate defaultA f (x ∷ xs) =
    op (f x) (aggregate defaultA f xs)

  measure :
    {A : Set} → A → Element A → Maybe Key
  measure defaultA datum = just (key defaultA datum)

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

  balanced :
    {A : Set} → A → Nat → Tree Key Element A → Set
  balanced defaultA balancing Empty = ⊤
  balanced defaultA balancing
    whole@(Node leftTree datum rightTree cachedHeight cachedMeasure) =
      (natToInt cachedHeight ≡ realHeight whole) ∧
      (cachedMeasure ≡
        aggregate
          (elementDefault defaultA)
          (measure defaultA)
          (seqModel whole)) ∧
      ((negateInt (natToInt balancing) ≤Z
          subtractInt (realHeight rightTree) (realHeight leftTree)) ∧
       (subtractInt (realHeight rightTree) (realHeight leftTree) ≤Z
          natToInt balancing)) ∧
      balanced defaultA balancing leftTree ∧
      balanced defaultA balancing rightTree

  module QueueContext
    (balancing : Nat)
    (balancingPositive : zeroZ <Z natToInt balancing)
    (Queue : Set → Set)
    (queueDefault : {A : Set} → A → Queue A)
    (repr :
      {A : Set} → A → Queue A → Tree Key Element A)
    (modelOf :
      {A : Set} → A → Queue A → Model (Element A))
    (queueInvariant :
      {A : Set} → (defaultA : A) → (self : Queue A) →
      balanced defaultA balancing (repr defaultA self) ∧
      (seq (modelOf defaultA self) ≡ seqModel (repr defaultA self)) ∧
      (hgt (modelOf defaultA self) ≡ realHeight (repr defaultA self)))
    (queueInj :
      {A : Set} → (defaultA : A) → (a b : Queue A) →
      ((repr defaultA a ≡ repr defaultA b) ∧
       (modelOf defaultA a ≡ modelOf defaultA b)) →
      a ≡ b)
    (count : {X : Set} → X → List X → Nat)
    (countNil : {X : Set} → (x : X) → count x [] ≡ zero)
    (countHit :
      {X : Set} → (x : X) → (xs : List X) →
      count x (x ∷ xs) ≡ suc (count x xs))
    (countMiss :
      {X : Set} → (x y : X) → (xs : List X) →
      x ≢ y →
      count x (y ∷ xs) ≡ count x xs)
    (getMinimumIndex :
      {A : Set} → A → List (Element A) → Int)
    (minimumIndexBounds :
      {A : Set} → (defaultA : A) → (values : List (Element A)) →
      natToInt (length values) ≢ zeroZ →
      (zeroZ ≤Z getMinimumIndex defaultA values) ∧
      (getMinimumIndex defaultA values <Z natToInt (length values)))
    (minimumIndexAggregate :
      {A : Set} → (defaultA : A) → (values : List (Element A)) →
      natToInt (length values) ≢ zeroZ →
      aggregate
        (elementDefault defaultA)
        (measure defaultA)
        values
      ≡ just
          (key defaultA
            (nthDefault
              (elementDefault defaultA)
              (intToNat (getMinimumIndex defaultA values))
              values)))
    (minimumIndexLeft :
      {A : Set} → (defaultA : A) → (values : List (Element A)) →
      natToInt (length values) ≢ zeroZ →
      lowerBoundStrict defaultA
        (key defaultA
          (nthDefault
            (elementDefault defaultA)
            (intToNat (getMinimumIndex defaultA values))
            values))
        (take (intToNat (getMinimumIndex defaultA values)) values))
    (minimumIndexRight :
      {A : Set} → (defaultA : A) → (values : List (Element A)) →
      natToInt (length values) ≢ zeroZ →
      lowerBound defaultA
        (key defaultA
          (nthDefault
            (elementDefault defaultA)
            (intToNat (getMinimumIndex defaultA values))
            values))
        (drop (intToNat (getMinimumIndex defaultA values)) values))
    where

    queueValues :
      {A : Set} → A → Queue A → List (Element A)
    queueValues defaultA queue = seq (modelOf defaultA queue)

    queueHeight :
      {A : Set} → A → Queue A → Int
    queueHeight defaultA queue = hgt (modelOf defaultA queue)

    toBag :
      {A : Set} → List (Element A) → Element A → Int
    toBag values datum = natToInt (count datum values)

    m3 :
      {A : Set} → A → Queue A → QueueSummary Element A
    m3 defaultA queue =
      let
        values = queueValues defaultA queue
      in
      queueSummary
        (toBag values)
        (nthDefault
          (elementDefault defaultA)
          (intToNat (getMinimumIndex defaultA values))
          values)
        (natToInt (length values))

    middleMatches :
      {A : Set} →
      Maybe (Element A) → Split (Element A) → Set
    middleMatches nothing parts = middlePart parts ≡ nothing
    middleMatches (just datum) parts = middlePart parts ≡ just datum

    present :
      {A : Set} → Maybe (Element A) → Set
    present nothing = ⊥
    present (just datum) = ⊤

    resultMatches :
      {A : Set} →
      Maybe (Element A) →
      Queue A →
      Maybe (Element A × Queue A) →
      Set
    resultMatches nothing remaining result = ⊥
    resultMatches (just datum) remaining result =
      result ≡ just (datum , remaining)

    emptySummary :
      {A : Set} → A → Queue A → Set
    emptySummary {A} defaultA queue =
      card (m3 defaultA queue) ≡ zeroZ ∧
      ((datum : Element A) → bag (m3 defaultA queue) datum ≡ zeroZ)

    successfulSummary :
      {A : Set} →
      A → Queue A → Element A → Queue A → Set
    successfulSummary {A} defaultA original datum remaining =
      card (m3 defaultA original) ≡
        addInt (card (m3 defaultA remaining)) oneZ ∧
      bag (m3 defaultA original) datum ≡
        addInt (bag (m3 defaultA remaining) datum) oneZ ∧
      datum ≡ minimum (m3 defaultA original) ∧
      ((other : Element A) →
        other ≢ datum →
        bag (m3 defaultA original) other ≡
          bag (m3 defaultA remaining) other)

    resultSummary :
      {A : Set} →
      A → Queue A → Maybe (Element A × Queue A) → Set
    resultSummary defaultA original nothing =
      emptySummary defaultA original
    resultSummary defaultA original (just (datum , remaining)) =
      successfulSummary defaultA original datum remaining

    recursivePremise :
      {A : Set} →
      A → Queue A → Split (Element A) →
      Maybe (Element A) → Queue A → Set
    recursivePremise defaultA original parts chosen remaining =
      (selected defaultA tt parts ∧
       rebuild parts ≡ queueValues defaultA original) ∧
      (queueValues defaultA remaining ≡
        append (leftPart parts) (rightPart parts)) ∧
      ((subtractInt
          (queueHeight defaultA original)
          (queueHeight defaultA remaining) ≤Z oneZ) ∧
       (zeroZ ≤Z
          subtractInt
            (queueHeight defaultA original)
            (queueHeight defaultA remaining))) ∧
      middleMatches chosen parts

    recursiveConclusion :
      {A : Set} →
      A → Queue A → Maybe (Element A) → Queue A → Set
    recursiveConclusion {A} defaultA original chosen remaining =
      present chosen ∧
      ((result : Maybe (Element A × Queue A)) →
        resultMatches chosen remaining result →
        resultSummary defaultA original result)

    nonemptyConclusion :
      {A : Set} → A → Queue A → Set
    nonemptyConclusion {A} defaultA original =
      selectionPossible tt (queueValues defaultA original) ∧
      ((parts : Split (Element A)) →
       (chosen : Maybe (Element A)) →
       (remaining : Queue A) →
       recursivePremise defaultA original parts chosen remaining →
       recursiveConclusion defaultA original chosen remaining)

    extract-min'vc : Set₁
    extract-min'vc =
      (A : Set) →
      (defaultA : A) →
      (original : Queue A) →
      (isEmpty : Bool) →
      (natToInt (length (queueValues defaultA original)) ≡ zeroZ →
        isEmpty ≡ true) →
      (isEmpty ≡ true → queueValues defaultA original ≡ []) →
      IfSet
        isEmpty
        (emptySummary defaultA original)
        (nonemptyConclusion defaultA original)
