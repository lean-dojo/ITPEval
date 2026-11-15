-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/avl/tables_MapBase_removeqtvc: the sorted sequence-map removal
-- verification condition relating a selected split and rebuilt AVL sequence
-- to map cardinality, membership, and retained stored values. This file contains no proof.

{-# OPTIONS --safe #-}

module tables_MapBase_removeqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ; _,_)

infix 4 _≤Z_ _<Z_
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

ifInt : Bool → Int → Int → Int
ifInt true when-true when-false = when-true
ifInt false when-true when-false = when-false

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

record Model (X : Set) : Set where
  constructor model
  field
    seq : List X
    hgt : Int

open Model

module MapBaseTheory
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
  (T2 : Set)
  (t2Default : T2)
  (Selector : Set)
  (selectorDefault : Selector)
  (Part : Set)
  (partDefault : Part)
  where

  infix 4 _≤K_ _<K_ _≈K_

  _≤K_ : Key → Key → Set
  _≤K_ = leKey

  _<K_ : Key → Key → Set
  x <K y = (x ≤K y) ∧ ((y ≤K x) → ⊥)

  _≈K_ : Key → Key → Set
  x ≈K y = (x ≤K y) ∧ (y ≤K x)

  selectionPossible :
    {X A : Set} → A → X → List (Element A) → Set
  selectionPossible defaultA ignored values =
    (i j : Int) →
    ((zeroZ ≤Z i) ∧ (i <Z j) ∧
      (j <Z natToInt (length values))) →
    key defaultA
      (nthDefault (elementDefault defaultA) (intToNat i) values)
      <K
    key defaultA
      (nthDefault (elementDefault defaultA) (intToNat j) values)

  upperBound :
    {A : Set} → A → Key → List (Element A) → Set
  upperBound defaultA upper values =
    (i : Int) →
    ((zeroZ ≤Z i) ∧ (i <Z natToInt (length values))) →
    key defaultA
      (nthDefault (elementDefault defaultA) (intToNat i) values)
      <K upper

  lowerBound :
    {A : Set} → A → Key → List (Element A) → Set
  lowerBound defaultA lower values =
    (i : Int) →
    ((zeroZ ≤Z i) ∧ (i <Z natToInt (length values))) →
    lower <K
      key defaultA
        (nthDefault (elementDefault defaultA) (intToNat i) values)

  selected :
    {A : Set} → A → Key → Split (Element A) → Set
  selected defaultA selectedKey parts with middlePart parts
  ... | nothing =
    upperBound defaultA selectedKey (leftPart parts) ∧
    lowerBound defaultA selectedKey (rightPart parts) ∧
    ⊤
  ... | just datum =
    upperBound defaultA selectedKey (leftPart parts) ∧
    lowerBound defaultA selectedKey (rightPart parts) ∧
    (selectedKey ≈K key defaultA datum)

  data Tree (A : Set) : Set where
    Empty : Tree A
    Node  :
      Tree A → Element A → Tree A → Nat → ⊤ → Tree A

  nodeModel :
    {A : Set} → List (Element A) → Element A →
    List (Element A) → List (Element A)
  nodeModel leftValues datum rightValues =
    append leftValues (datum ∷ rightValues)

  seqModel : {A : Set} → Tree A → List (Element A)
  seqModel Empty = []
  seqModel (Node leftTree datum rightTree _ _) =
    nodeModel (seqModel leftTree) datum (seqModel rightTree)

  realHeight : {A : Set} → Tree A → Int
  realHeight Empty = zeroZ
  realHeight (Node leftTree _ rightTree _ _) =
    addInt oneZ (maxInt (realHeight leftTree) (realHeight rightTree))

  balanced : {A : Set} → Tree A → Set
  balanced Empty = ⊤
  balanced whole@(Node leftTree _ rightTree cachedHeight cachedUnit) =
    (natToInt cachedHeight ≡ realHeight whole) ∧
    (cachedUnit ≡ tt) ∧
    ((negateInt (natToInt balancing) ≤Z
        subtractInt (realHeight rightTree) (realHeight leftTree)) ∧
     (subtractInt (realHeight rightTree) (realHeight leftTree) ≤Z
        natToInt balancing)) ∧
    balanced leftTree ∧
    balanced rightTree

  Domain :
    {A : Set} → A → List (Element A) → Key → Set
  Domain defaultA values soughtKey =
    Σ Int λ i →
      ((zeroZ ≤Z i) ∧ (i <Z natToInt (length values))) ∧
      (key defaultA
        (nthDefault
          (elementDefault defaultA)
          (intToNat i)
          values)
        ≈K soughtKey)

  record MapModel (A : Set) : Set where
    constructor mapModel
    field
      domn : Key → Bool
      func : Key → Element A
      card : Int

  open MapModel

  module Implementation
    (T3 : Set → Set)
    (t3Default : {A : Set} → A → T3 A)
    (repr : {A : Set} → A → T3 A → Tree A)
    (m1 : {A : Set} → A → T3 A → Model (Element A))
    (tInvariant :
      {A : Set} → (defaultA : A) → (self : T3 A) →
      balanced (repr defaultA self) ∧
      (seq (m1 defaultA self) ≡ seqModel (repr defaultA self)) ∧
      (hgt (m1 defaultA self) ≡ realHeight (repr defaultA self)))
    (tInj :
      {A : Set} → (defaultA : A) → (a b : T3 A) →
      ((repr defaultA a ≡ repr defaultA b) ∧
       (m1 defaultA a ≡ m1 defaultA b)) →
      a ≡ b)
    (MapBase : Set → Set)
    (mapBaseDefault : {A : Set} → A → MapBase A)
    (mapField : {A : Set} → A → MapBase A → T3 A)
    (mapInvariant :
      {A : Set} → (defaultA : A) → (self : MapBase A) →
      selectionPossible defaultA tt
        (seq (m1 defaultA (mapField defaultA self))))
    (mapInj :
      {A : Set} → (defaultA : A) → (a b : MapBase A) →
      mapField defaultA a ≡ mapField defaultA b →
      a ≡ b)
    (makeFunc :
      {A : Set} → A → List (Element A) → Key → Element A)
    (makeFuncSpec :
      {A : Set} → (defaultA : A) →
      (values : List (Element A)) → (soughtKey : Key) → (i : Int) →
      selectionPossible defaultA tt values →
      Domain defaultA values soughtKey →
      zeroZ ≤Z i →
      i <Z natToInt (length values) →
      key defaultA
        (nthDefault
          (elementDefault defaultA)
          (intToNat i)
          values)
        ≈K soughtKey →
      makeFunc defaultA values soughtKey ≡
        nthDefault
          (elementDefault defaultA)
          (intToNat i)
          values)
    (domainClosure :
      {A : Set} → A → List (Element A) → Key → Bool)
    (makeFuncClosure :
      {A : Set} → A → List (Element A) → Key → Element A)
    (domainClosureDef :
      {A : Set} → (defaultA : A) →
      (values : List (Element A)) → (soughtKey : Key) →
      (domainClosure defaultA values soughtKey ≡ true) →
      Domain defaultA values soughtKey)
    (domainClosureDefBack :
      {A : Set} → (defaultA : A) →
      (values : List (Element A)) → (soughtKey : Key) →
      Domain defaultA values soughtKey →
      domainClosure defaultA values soughtKey ≡ true)
    (makeFuncClosureDef :
      {A : Set} → (defaultA : A) →
      (values : List (Element A)) → (soughtKey : Key) →
      makeFuncClosure defaultA values soughtKey ≡
      makeFunc defaultA values soughtKey)
    where

    data View (A : Set) : Set where
      AEmpty : View A
      ANode  :
        T3 A → Element A → T3 A → Nat → ⊤ → View A

    m3 :
      {A : Set} → A → MapBase A → MapModel A
    m3 defaultA value =
      let values = seq (m1 defaultA (mapField defaultA value))
      in
      mapModel
        (domainClosure defaultA values)
        (makeFuncClosure defaultA values)
        (natToInt (length values))

    remove'vc : Set₁
    remove'vc =
      (A : Set) →
      (defaultA : A) →
      (t5 : MapBase A) →
      (k0 : Key) →
      let
        original = mapField defaultA t5
        originalModel = m3 defaultA t5
      in
      selectionPossible defaultA k0
        (seq (m1 defaultA original)) ∧
      ((parts : Split (Element A)) →
       (removedTree : T3 A) →
       ((seq (m1 defaultA removedTree) ≡
          append (leftPart parts) (rightPart parts)) ∧
        (selected defaultA k0 parts ∧
         rebuild parts ≡ seq (m1 defaultA original)) ∧
        (subtractInt
          (hgt (m1 defaultA original))
          (hgt (m1 defaultA removedTree)) ≤Z oneZ) ∧
        (zeroZ ≤Z
          subtractInt
            (hgt (m1 defaultA original))
            (hgt (m1 defaultA removedTree)))) →
       selectionPossible defaultA tt
         (seq (m1 defaultA removedTree)) ∧
       ((result : MapBase A) →
        mapField defaultA result ≡ removedTree →
        let resultModel = m3 defaultA result
        in
        (card resultModel ≡
          ifInt
            (domn originalModel k0)
            (subtractInt (card originalModel) oneZ)
            (card originalModel)) ∧
        ((k : Key) →
          (k ≈K k0) →
          (domn resultModel k ≡ true) →
          ⊥) ∧
        ((domn resultModel k0 ≡ true) → ⊥) ∧
        ((k : Key) →
          ((k ≈K k0) → ⊥) →
          (domn resultModel k ≡ true) ↔
          (domn originalModel k ≡ true)) ∧
        ((k : Key) →
          (((k ≈K k0) → ⊥) ∧
           (domn resultModel k ≡ true)) →
          func resultModel k ≡ func originalModel k)))
