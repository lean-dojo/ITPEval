-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/avl/avl_AVL_snocqtvc: an AVL-tree append-at-end verification
-- condition relating view invariants to right-subtree insertion, balance
-- bounds, sequence construction, and cached-height growth. This file contains no proof.

{-# OPTIONS --safe #-}

module avl_AVL_snocqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ)

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
nodeModel left datum right = append left (datum ∷ right)

seqModel :
  {T : Set} {T1 : Set → Set} {A : Set} →
  Tree T T1 A → List (T1 A)
seqModel Empty = []
seqModel (Node left datum right _ _) =
  nodeModel (seqModel left) datum (seqModel right)

realHeight :
  {T : Set} {T1 : Set → Set} {A : Set} →
  Tree T T1 A → Int
realHeight Empty = zeroZ
realHeight (Node left _ right _ _) =
  addInt oneZ (maxInt (realHeight left) (realHeight right))

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
  whole@(Node left datum right cachedHeight cachedMeasure) =
    (natToInt cachedHeight ≡ realHeight whole) ∧
    (cachedMeasure ≡
      agg
        (t1Default defaultA)
        (measureClosure defaultA)
        (seqModel whole)) ∧
    ((negateInt (natToInt balancing) ≤Z
        subtractInt (realHeight right) (realHeight left)) ∧
     (subtractInt (realHeight right) (realHeight left) ≤Z
        natToInt balancing)) ∧
    balanced defaultA t1Default agg measureClosure balancing left ∧
    balanced defaultA t1Default agg measureClosure balancing right

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
  where

  data View (A : Set) : Set where
    AEmpty : View A
    ANode  : T2 A → T1 A → T2 A → Nat → T → View A

  seqOf :
    {A : Set} → A → T2 A → List (T1 A)
  seqOf defaultA x = seq (m1 defaultA x)

  heightOf :
    {A : Set} → A → T2 A → Int
  heightOf defaultA x = hgt (m1 defaultA x)

  heightBalance :
    {A : Set} → A → T2 A → T2 A → Set
  heightBalance defaultA left right =
    (negateInt (natToInt balancing) ≤Z
      subtractInt
        (heightOf defaultA left)
        (heightOf defaultA right)) ∧
    (subtractInt
      (heightOf defaultA left)
      (heightOf defaultA right) ≤Z natToInt balancing)

  viewFact :
    {A : Set} → A → View A → T2 A → Set
  viewFact defaultA AEmpty subject =
    (heightOf defaultA subject ≡ zeroZ) ∧
    (seqOf defaultA subject ≡ [])
  viewFact defaultA
    (ANode left datum right height summary) subject =
      (seqOf defaultA subject ≡
        nodeModel
          (seqOf defaultA left)
          datum
          (seqOf defaultA right)) ∧
      (summary ≡
        agg
          (t1Default defaultA)
          (measureClosure defaultA)
          (seqOf defaultA subject)) ∧
      (heightBalance defaultA left right) ∧
      (heightOf defaultA subject ≡ natToInt height) ∧
      (natToInt height ≡
        addInt oneZ
          (maxInt
            (heightOf defaultA left)
            (heightOf defaultA right)))

  childInsertion :
    {A : Set} → A → T2 A → T1 A → T2 A → Set
  childInsertion defaultA right datum child =
    (seqOf defaultA child ≡
      append (seqOf defaultA right) (datum ∷ [])) ∧
    (subtractInt
      (heightOf defaultA child)
      (heightOf defaultA right) ≤Z oneZ) ∧
    (zeroZ ≤Z
      subtractInt
        (heightOf defaultA child)
        (heightOf defaultA right))

  widenedBalance :
    {A : Set} → A → T2 A → T2 A → Set
  widenedBalance defaultA left right =
    (subtractInt
      (negateInt (natToInt balancing))
      oneZ ≤Z
        subtractInt
          (heightOf defaultA left)
          (heightOf defaultA right)) ∧
    (subtractInt
      (heightOf defaultA left)
      (heightOf defaultA right) ≤Z
        addInt (natToInt balancing) oneZ)

  nonemptySafety :
    {A : Set} → A → View A → T2 A → T1 A → Set
  nonemptySafety defaultA AEmpty subject datum = ⊤
  nonemptySafety defaultA
    (ANode left _ right _ _) subject datum =
      ((zeroZ ≤Z heightOf defaultA subject) ∧
       (heightOf defaultA right <Z heightOf defaultA subject)) ∧
      ((child : T2 _) →
        childInsertion defaultA right datum child →
        widenedBalance defaultA left child)

  resultPremise :
    {A : Set} → A →
    View A → T1 A → T2 A → Set
  resultPremise defaultA AEmpty datum result =
    (seqOf defaultA result ≡ datum ∷ []) ∧
    (heightOf defaultA result ≡ oneZ)
  resultPremise defaultA
    (ANode left rootDatum right _ _) datum result =
      Σ (T2 _) λ child →
        childInsertion defaultA right datum child ∧
        (seqOf defaultA result ≡
          nodeModel
            (seqOf defaultA left)
            rootDatum
            (seqOf defaultA child)) ∧
        let
          leftHeight = heightOf defaultA left
          childHeight = heightOf defaultA child
          expectedHeight =
            addInt oneZ (maxInt leftHeight childHeight)
          resultHeight = heightOf defaultA result
        in
        ((zeroZ ≤Z subtractInt expectedHeight resultHeight) ∧
         (subtractInt expectedHeight resultHeight ≤Z oneZ)) ∧
        (heightBalance defaultA left child →
          expectedHeight ≡ resultHeight)

  resultConclusion :
    {A : Set} → A → T2 A → T1 A → T2 A → Set
  resultConclusion defaultA subject datum result =
    (seqOf defaultA result ≡
      append (seqOf defaultA subject) (datum ∷ [])) ∧
    (subtractInt
      (heightOf defaultA result)
      (heightOf defaultA subject) ≤Z oneZ) ∧
    (zeroZ ≤Z
      subtractInt
        (heightOf defaultA result)
        (heightOf defaultA subject))

  snoc'vc : Set₁
  snoc'vc =
    (A : Set) →
    (defaultA : A) →
    (o1 : View A) →
    (subject : T2 A) →
    (datum : T1 A) →
    viewFact defaultA o1 subject →
    nonemptySafety defaultA o1 subject datum ∧
    ((result : T2 A) →
      resultPremise defaultA o1 datum result →
      resultConclusion defaultA subject datum result)
