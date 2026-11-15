-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/avl/avl_AVL_insertqtvc: an AVL-tree insertion verification condition
-- for selector-guided sequence splitting, reconstruction, and height growth.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module avl_AVL_insertqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

data ⊤ : Set where
  tt : ⊤

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

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

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) = nthDefault default n xs

record Split (A : Set) : Set where
  constructor split
  field
    left   : List A
    middle : Maybe A
    right  : List A

open Split

optionToList : {A : Set} → Maybe A → List A
optionToList nothing = []
optionToList (just x) = x ∷ []

rebuild : {A : Set} → Split A → List A
rebuild parts =
  append (left parts) (append (optionToList (middle parts)) (right parts))

leftExtend : {A : Set} → List A → A → Split A → Split A
leftExtend prefix datum parts =
  split
    (append prefix (datum ∷ left parts))
    (middle parts)
    (right parts)

rightExtend : {A : Set} → Split A → A → List A → Split A
rightExtend parts datum suffix =
  split
    (left parts)
    (middle parts)
    (append (right parts) (datum ∷ suffix))

data PartBase (A : Set) : Set where
  Left  : A → PartBase A
  Right : A → PartBase A
  Here  : PartBase A

record Model (X : Set) : Set where
  constructor model
  field
    seq : List X
    hgt : Int

open Model

data Tree (T : Set) (T1 : Set → Set) (A : Set) : Set where
  Empty : Tree T T1 A
  Node  : Tree T T1 A → T1 A → Tree T T1 A → Nat → T →
          Tree T T1 A

nodeModel : {A : Set} → List A → A → List A → List A
nodeModel leftValues datum rightValues =
  append leftValues (datum ∷ rightValues)

seqModel :
  {T : Set} {T1 : Set → Set} {A : Set} →
  Tree T T1 A → List (T1 A)
seqModel Empty = []
seqModel (Node leftTree datum rightTree _ _) =
  nodeModel (seqModel leftTree) datum (seqModel rightTree)

realHeight :
  {T : Set} {T1 : Set → Set} {A : Set} →
  Tree T T1 A → Int
realHeight Empty = zeroZ
realHeight (Node leftTree _ rightTree _ _) =
  addInt oneZ (maxInt (realHeight leftTree) (realHeight rightTree))

balanced :
  {T : Set} {T1 : Set → Set} {A : Set} →
  (defaultA : A) →
  ({X : Set} → X → T1 X) →
  (agg : {X : Set} → X → (X → T) → List X → T) →
  ({X : Set} → X → T1 X → T) →
  Nat →
  Tree T T1 A →
  Set
balanced defaultA t1Default agg measureClosure balancing Empty = ⊤
balanced defaultA t1Default agg measureClosure balancing
  whole@(Node leftTree datum rightTree cachedHeight cachedMeasure) =
    (natToInt cachedHeight ≡ realHeight whole) ∧
    (cachedMeasure ≡
      agg
        (t1Default defaultA)
        (measureClosure defaultA)
        (seqModel whole)) ∧
    ((negateInt (natToInt balancing) ≤Z
        subtractInt (realHeight rightTree) (realHeight leftTree)) ∧
     (subtractInt (realHeight rightTree) (realHeight leftTree) ≤Z
        natToInt balancing)) ∧
    balanced defaultA t1Default agg measureClosure balancing leftTree ∧
    balanced defaultA t1Default agg measureClosure balancing rightTree

module AVLTheory
  (T : Set)
  (zeroT : T)
  (op : T → T → T)
  (assoc :
    (a b c : T) → op a (op b c) ≡ op (op a b) c)
  (neutral :
    (x : T) → (op x zeroT ≡ x) ∧ (x ≡ op zeroT x))
  (agg :
    {A : Set} → A → (A → T) → List A → T)
  (aggEmpty :
    {A : Set} → (defaultA : A) → (f : A → T) →
    agg defaultA f [] ≡ zeroT)
  (aggSing :
    {A : Set} → (defaultA : A) → (s : List A) → (f : A → T) →
    natToInt (length s) ≡ oneZ →
    agg defaultA f s ≡ f (nthDefault defaultA zero s))
  (aggCat :
    {A : Set} → (defaultA : A) → (f : A → T) →
    (s1 s2 : List A) →
    agg defaultA f (append s1 s2) ≡
      op (agg defaultA f s1) (agg defaultA f s2))
  (T1 : Set → Set)
  (t1Default : {A : Set} → A → T1 A)
  (measure : {A : Set} → A → T1 A → T)
  (balancing : Nat)
  (balancingDef : zeroZ <Z natToInt balancing)
  (measureClosure : {A : Set} → A → T1 A → T)
  (measureClosureDef :
    {A : Set} → (defaultA : A) → (y : T1 A) →
    measureClosure defaultA y ≡ measure defaultA y)
  (T2 : Set → Set)
  (t2Default : {A : Set} → A → T2 A)
  (repr :
    {A : Set} → A → T2 A → Tree T T1 A)
  (m1 :
    {A : Set} → A → T2 A → Model (T1 A))
  (tInvariant :
    {A : Set} → (defaultA : A) → (self : T2 A) →
    balanced defaultA t1Default agg measureClosure balancing
      (repr defaultA self) ∧
    (seq (m1 defaultA self) ≡ seqModel (repr defaultA self)) ∧
    (hgt (m1 defaultA self) ≡ realHeight (repr defaultA self)))
  (tInj :
    {A : Set} → (defaultA : A) → (a b : T2 A) →
    ((repr defaultA a ≡ repr defaultA b) ∧
     (m1 defaultA a ≡ m1 defaultA b)) →
    a ≡ b)
  (Selector : Set)
  (selectorDefault : Selector)
  (selected :
    {A : Set} → A → Selector → Split (T1 A) → Set)
  (selectionPossible :
    {A : Set} → A → Selector → List (T1 A) → Set)
  (selectionEmpty :
    {A : Set} → (defaultA : A) → (selector : Selector) →
    selectionPossible defaultA selector [] →
    selected defaultA selector (split [] nothing []))
  where

  data View (A : Set) : Set where
    AEmpty : View A
    ANode  : T2 A → T1 A → T2 A → Nat → T → View A

  seqOf :
    {A : Set} → A → T2 A → List (T1 A)
  seqOf defaultA value = seq (m1 defaultA value)

  heightOf :
    {A : Set} → A → T2 A → Int
  heightOf defaultA value = hgt (m1 defaultA value)

  heightBalance :
    {A : Set} → A → T2 A → T2 A → Set
  heightBalance defaultA leftTree rightTree =
    (negateInt (natToInt balancing) ≤Z
      subtractInt
        (heightOf defaultA leftTree)
        (heightOf defaultA rightTree)) ∧
    (subtractInt
      (heightOf defaultA leftTree)
      (heightOf defaultA rightTree) ≤Z
        natToInt balancing)

  widenedBalance :
    {A : Set} → A → T2 A → T2 A → Set
  widenedBalance defaultA leftTree rightTree =
    (subtractInt
      (negateInt (natToInt balancing))
      oneZ ≤Z
        subtractInt
          (heightOf defaultA leftTree)
          (heightOf defaultA rightTree)) ∧
    (subtractInt
      (heightOf defaultA leftTree)
      (heightOf defaultA rightTree) ≤Z
        addInt (natToInt balancing) oneZ)

  heightGrowth :
    {A : Set} → A → T2 A → T2 A → Set
  heightGrowth defaultA original result =
    (subtractInt
      (heightOf defaultA result)
      (heightOf defaultA original) ≤Z oneZ) ∧
    (zeroZ ≤Z
      subtractInt
        (heightOf defaultA result)
        (heightOf defaultA original))

  viewFact :
    {A : Set} → A → View A → T2 A → Set
  viewFact defaultA AEmpty subject =
    (heightOf defaultA subject ≡ zeroZ) ∧
    (seqOf defaultA subject ≡ [])
  viewFact defaultA
    (ANode leftTree datum rightTree height summary) subject =
      (seqOf defaultA subject ≡
        nodeModel
          (seqOf defaultA leftTree)
          datum
          (seqOf defaultA rightTree)) ∧
      (summary ≡
        agg
          (t1Default defaultA)
          (measureClosure defaultA)
          (seqOf defaultA subject)) ∧
      (heightBalance defaultA leftTree rightTree) ∧
      (heightOf defaultA subject ≡ natToInt height) ∧
      (natToInt height ≡
        addInt oneZ
          (maxInt
            (heightOf defaultA leftTree)
            (heightOf defaultA rightTree)))

  insertionResult :
    {A : Set} → A →
    Selector → T2 A → T2 A → Split (T1 A) → T1 A → Set
  insertionResult
    defaultA selector original result parts insertedDatum =
      (seqOf defaultA result ≡
        nodeModel (left parts) insertedDatum (right parts)) ∧
      (selected defaultA selector parts ∧
       rebuild parts ≡ seqOf defaultA original) ∧
      heightGrowth defaultA original result

  recursivePremise :
    {A : Set} → A →
    Selector → T2 A → Split (T1 A) → T1 A → T2 A → Set
  recursivePremise
    defaultA selector subtree parts insertedDatum result =
      (seqOf defaultA result ≡
        nodeModel (left parts) insertedDatum (right parts)) ∧
      (selected defaultA selector parts ∧
       rebuild parts ≡ seqOf defaultA subtree) ∧
      heightGrowth defaultA subtree result

  nodeResultPremise :
    {A : Set} → A →
    T2 A → T1 A → T2 A → T2 A → Set
  nodeResultPremise defaultA leftTree datum rightTree result =
    (seqOf defaultA result ≡
      nodeModel
        (seqOf defaultA leftTree)
        datum
        (seqOf defaultA rightTree)) ∧
    let
      leftHeight = heightOf defaultA leftTree
      rightHeight = heightOf defaultA rightTree
      expectedHeight = addInt oneZ (maxInt leftHeight rightHeight)
      resultHeight = heightOf defaultA result
    in
    ((zeroZ ≤Z subtractInt expectedHeight resultHeight) ∧
     (subtractInt expectedHeight resultHeight ≤Z oneZ)) ∧
    (heightBalance defaultA leftTree rightTree →
      expectedHeight ≡ resultHeight)

  hereResultPremise :
    {A : Set} → A →
    T2 A → T1 A → T2 A → T2 A → Set
  hereResultPremise defaultA leftTree insertedDatum rightTree result =
    (seqOf defaultA result ≡
      nodeModel
        (seqOf defaultA leftTree)
        insertedDatum
        (seqOf defaultA rightTree)) ∧
    (heightOf defaultA result ≡
      addInt oneZ
        (maxInt
          (heightOf defaultA leftTree)
          (heightOf defaultA rightTree)))

  dispatchPremise :
    {A : Set} → A →
    Selector → List (T1 A) → T1 A → List (T1 A) →
    PartBase Selector → Set
  dispatchPremise defaultA selector leftValues datum rightValues Here =
    selected defaultA selector
      (split leftValues (just datum) rightValues)
  dispatchPremise defaultA selector leftValues datum rightValues
    (Left leftSelector) =
      selectionPossible defaultA leftSelector leftValues ∧
      ((parts : Split (T1 _)) →
        (selected defaultA leftSelector parts ∧
         rebuild parts ≡ leftValues) →
        selected defaultA selector
          (rightExtend parts datum rightValues))
  dispatchPremise defaultA selector leftValues datum rightValues
    (Right rightSelector) =
      selectionPossible defaultA rightSelector rightValues ∧
      ((parts : Split (T1 _)) →
        (selected defaultA rightSelector parts ∧
         rebuild parts ≡ rightValues) →
        selected defaultA selector
          (leftExtend leftValues datum parts))

  leftDispatchConclusion :
    {A : Set} → A →
    Selector → Selector → T2 A → T2 A → T1 A → T2 A → T1 A → Set
  leftDispatchConclusion
    defaultA selector leftSelector subject leftTree rootDatum
    rightTree insertedDatum =
      (((zeroZ ≤Z heightOf defaultA subject) ∧
        (heightOf defaultA leftTree <Z heightOf defaultA subject)) ∧
       selectionPossible defaultA leftSelector (seqOf defaultA leftTree)) ∧
      ((parts : Split (T1 _)) →
       (newLeft : T2 _) →
       recursivePremise
         defaultA leftSelector leftTree parts insertedDatum newLeft →
       widenedBalance defaultA newLeft rightTree ∧
       ((result : T2 _) →
        nodeResultPremise defaultA newLeft rootDatum rightTree result →
        insertionResult
          defaultA
          selector
          subject
          result
          (rightExtend parts rootDatum (seqOf defaultA rightTree))
          insertedDatum))

  rightDispatchConclusion :
    {A : Set} → A →
    Selector → Selector → T2 A → T2 A → T1 A → T2 A → T1 A → Set
  rightDispatchConclusion
    defaultA selector rightSelector subject leftTree rootDatum
    rightTree insertedDatum =
      (((zeroZ ≤Z heightOf defaultA subject) ∧
        (heightOf defaultA rightTree <Z heightOf defaultA subject)) ∧
       selectionPossible defaultA rightSelector (seqOf defaultA rightTree)) ∧
      ((parts : Split (T1 _)) →
       (newRight : T2 _) →
       recursivePremise
         defaultA rightSelector rightTree parts insertedDatum newRight →
       widenedBalance defaultA leftTree newRight ∧
       ((result : T2 _) →
        nodeResultPremise defaultA leftTree rootDatum newRight result →
        insertionResult
          defaultA
          selector
          subject
          result
          (leftExtend (seqOf defaultA leftTree) rootDatum parts)
          insertedDatum))

  hereDispatchConclusion :
    {A : Set} → A →
    Selector → T2 A → T2 A → T1 A → T2 A → T1 A → Set
  hereDispatchConclusion
    defaultA selector subject leftTree rootDatum rightTree insertedDatum =
      heightBalance defaultA leftTree rightTree ∧
      ((result : T2 _) →
        hereResultPremise
          defaultA leftTree insertedDatum rightTree result →
        insertionResult
          defaultA
          selector
          subject
          result
          (split
            (seqOf defaultA leftTree)
            (just rootDatum)
            (seqOf defaultA rightTree))
          insertedDatum)

  dispatchConclusion :
    {A : Set} → A →
    Selector → T2 A → T2 A → T1 A → T2 A → T1 A →
    PartBase Selector → Set
  dispatchConclusion
    defaultA selector subject leftTree rootDatum rightTree insertedDatum
    (Left leftSelector) =
      leftDispatchConclusion
        defaultA selector leftSelector subject leftTree rootDatum
        rightTree insertedDatum
  dispatchConclusion
    defaultA selector subject leftTree rootDatum rightTree insertedDatum
    (Right rightSelector) =
      rightDispatchConclusion
        defaultA selector rightSelector subject leftTree rootDatum
        rightTree insertedDatum
  dispatchConclusion
    defaultA selector subject leftTree rootDatum rightTree insertedDatum
    Here =
      hereDispatchConclusion
        defaultA selector subject leftTree rootDatum rightTree insertedDatum

  nodeConclusion :
    {A : Set} → A →
    Selector → T2 A → T2 A → T1 A → T2 A → T1 A → Set
  nodeConclusion
    defaultA selector subject leftTree rootDatum rightTree insertedDatum =
    let
      rightValues = seqOf defaultA rightTree
      leftValues = seqOf defaultA leftTree
    in
    (selectionPossible defaultA selector
      (nodeModel leftValues rootDatum rightValues) ∧
     (agg
        (t1Default defaultA)
        (measureClosure defaultA)
        (seqOf defaultA leftTree) ≡
      agg
        (t1Default defaultA)
        (measureClosure defaultA)
        leftValues) ∧
     (agg
        (t1Default defaultA)
        (measureClosure defaultA)
        (seqOf defaultA rightTree) ≡
      agg
        (t1Default defaultA)
        (measureClosure defaultA)
        rightValues)) ∧
    ((branch : PartBase Selector) →
      dispatchPremise
        defaultA selector leftValues rootDatum rightValues branch →
      dispatchConclusion
        defaultA selector subject leftTree rootDatum rightTree
        insertedDatum branch)

  emptyConclusion :
    {A : Set} → A →
    Selector → T2 A → T1 A → Set
  emptyConclusion {A} defaultA selector subject insertedDatum =
    (result : T2 A) →
    ((seqOf defaultA result ≡ insertedDatum ∷ []) ∧
     (heightOf defaultA result ≡ oneZ)) →
    insertionResult
      defaultA
      selector
      subject
      result
      (split [] nothing [])
      insertedDatum

  conclusion :
    {A : Set} → A →
    Selector → T2 A → View A → T1 A → Set
  conclusion defaultA selector subject AEmpty insertedDatum =
    emptyConclusion
      defaultA selector subject insertedDatum
  conclusion defaultA selector subject
    (ANode leftTree rootDatum rightTree _ _) insertedDatum =
      nodeConclusion
        defaultA selector subject leftTree rootDatum rightTree insertedDatum

  insert'vc : Set₁
  insert'vc =
    (A : Set) →
    (defaultA : A) →
    (selector : Selector) →
    (subject : T2 A) →
    (view : View A) →
    (insertedDatum : T1 A) →
    selectionPossible defaultA selector (seqOf defaultA subject) →
    viewFact defaultA view subject →
    conclusion defaultA selector subject view insertedDatum
