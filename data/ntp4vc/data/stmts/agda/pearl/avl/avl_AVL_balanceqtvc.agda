-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/avl/avl_AVL_balanceqtvc: an AVL-tree balancing verification condition
-- for single and double rotations, sequence preservation, and cached heights.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module avl_AVL_balanceqtvc where

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

data ⊥ : Set where

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

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
      subtractInt (heightOf defaultA left) (heightOf defaultA right)) ∧
    (subtractInt (heightOf defaultA left) (heightOf defaultA right) ≤Z
      natToInt balancing)

  nodeSpec :
    {A : Set} → A →
    T2 A → T1 A → T2 A → T2 A → Set
  nodeSpec defaultA left datum right result =
    (seqOf defaultA result ≡
      nodeModel
        (seqOf defaultA left)
        datum
        (seqOf defaultA right)) ∧
    (heightOf defaultA result ≡
      addInt oneZ
        (maxInt
          (heightOf defaultA left)
          (heightOf defaultA right)))

  viewFact :
    {A : Set} → A → View A → T2 A → Set
  viewFact defaultA AEmpty subject =
    (heightOf defaultA subject ≡ zeroZ) ∧
    (seqOf defaultA subject ≡ [])
  viewFact defaultA (ANode left datum right height summary) subject =
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

  leftDoubleSafety :
    {A : Set} → A →
    View A → T2 A → T1 A → T2 A → T1 A → Set
  leftDoubleSafety defaultA AEmpty ll ld r d = ⊥
  leftDoubleSafety defaultA
    (ANode lrl lrd lrr _ _) ll ld r d =
      heightBalance defaultA lrr r ∧
      ((o6 : T2 _) →
        nodeSpec defaultA lrr d r o6 →
        heightBalance defaultA ll lrl ∧
        ((o7 : T2 _) →
          nodeSpec defaultA ll ld lrl o7 →
          heightBalance defaultA o7 o6))

  leftSafety :
    {A : Set} → A → View A → T2 A → T1 A → Set
  leftSafety defaultA AEmpty r d = ⊥
  leftSafety defaultA (ANode ll ld lr _ _) r d =
    (o3 : Int) →
    o3 ≡ heightOf defaultA lr →
    (o4 : Int) →
    o4 ≡ heightOf defaultA ll →
    IfSet
      (intLessOrEqual o3 o4)
      (heightBalance defaultA lr r ∧
       ((o5 : T2 _) →
        nodeSpec defaultA lr d r o5 →
        heightBalance defaultA ll o5))
      ((o5 : View _) →
        viewFact defaultA o5 lr →
        leftDoubleSafety defaultA o5 ll ld r d)

  rightDoubleSafety :
    {A : Set} → A →
    View A → T2 A → T1 A → T2 A → T1 A → Set
  rightDoubleSafety defaultA AEmpty l d rr rd = ⊥
  rightDoubleSafety defaultA
    (ANode rll rld rlr _ _) l d rr rd =
      heightBalance defaultA rlr rr ∧
      ((o7 : T2 _) →
        nodeSpec defaultA rlr rd rr o7 →
        heightBalance defaultA l rll ∧
        ((o8 : T2 _) →
          nodeSpec defaultA l d rll o8 →
          heightBalance defaultA o8 o7))

  rightSafety :
    {A : Set} → A → T2 A → T1 A → View A → Set
  rightSafety defaultA l d AEmpty = ⊥
  rightSafety defaultA l d (ANode rl rd rr _ _) =
    (o4 : Int) →
    o4 ≡ heightOf defaultA rl →
    (o5 : Int) →
    o5 ≡ heightOf defaultA rr →
    IfSet
      (intLessOrEqual o4 o5)
      (heightBalance defaultA l rl ∧
       ((o6 : T2 _) →
        nodeSpec defaultA l d rl o6 →
        heightBalance defaultA o6 rr))
      ((o6 : View _) →
        viewFact defaultA o6 rl →
        rightDoubleSafety defaultA o6 l d rr rd)

  safety :
    {A : Set} → A →
    T2 A → T2 A → T1 A → Int → Set
  safety defaultA l r d df =
    IfSet
      (intLess (natToInt balancing) df)
      ((o2 : View _) →
        viewFact defaultA o2 l →
        leftSafety defaultA o2 r d)
      ((o2 : Int) →
        o2 ≡ negateInt (natToInt balancing) →
        IfSet
          (intLess df o2)
          ((o3 : View _) →
            viewFact defaultA o3 r →
            rightSafety defaultA l d o3)
          (heightBalance defaultA l r))

  leftDoubleConstruction :
    {A : Set} → A →
    View A → T2 A → T1 A → T2 A → T1 A → T2 A → Set
  leftDoubleConstruction defaultA AEmpty ll ld r d result = ⊥
  leftDoubleConstruction defaultA
    (ANode lrl lrd lrr _ _) ll ld r d result =
      Σ (T2 _) λ o6 →
        nodeSpec defaultA lrr d r o6 ∧
        Σ (T2 _) λ o7 →
          nodeSpec defaultA ll ld lrl o7 ∧
          nodeSpec defaultA o7 lrd o6 result

  leftConstructionFromView :
    {A : Set} → A →
    View A → T2 A → T1 A → T2 A → Set
  leftConstructionFromView defaultA AEmpty r d result = ⊥
  leftConstructionFromView defaultA (ANode ll ld lr _ _) r d result =
    Σ Int λ o3 →
      (o3 ≡ heightOf defaultA lr) ∧
      Σ Int λ o4 →
        (o4 ≡ heightOf defaultA ll) ∧
        IfSet
          (intLessOrEqual o3 o4)
          (Σ (T2 _) λ o5 →
            nodeSpec defaultA lr d r o5 ∧
            nodeSpec defaultA ll ld o5 result)
          (Σ (View _) λ o5 →
            viewFact defaultA o5 lr ∧
            leftDoubleConstruction defaultA o5 ll ld r d result)

  leftConstruction :
    {A : Set} → A →
    T2 A → T2 A → T1 A → T2 A → Set
  leftConstruction defaultA l r d result =
    Σ (View _) λ o2 →
      viewFact defaultA o2 l ∧
      leftConstructionFromView defaultA o2 r d result

  rightDoubleConstruction :
    {A : Set} → A →
    View A → T2 A → T1 A → T2 A → T1 A → T2 A → Set
  rightDoubleConstruction defaultA AEmpty l d rr rd result = ⊥
  rightDoubleConstruction defaultA
    (ANode rll rld rlr _ _) l d rr rd result =
      Σ (T2 _) λ o7 →
        nodeSpec defaultA rlr rd rr o7 ∧
        Σ (T2 _) λ o8 →
          nodeSpec defaultA l d rll o8 ∧
          nodeSpec defaultA o8 rld o7 result

  rightConstructionFromView :
    {A : Set} → A →
    T2 A → T1 A → View A → T2 A → Set
  rightConstructionFromView defaultA l d AEmpty result = ⊥
  rightConstructionFromView defaultA l d
    (ANode rl rd rr _ _) result =
      Σ Int λ o4 →
        (o4 ≡ heightOf defaultA rl) ∧
        Σ Int λ o5 →
          (o5 ≡ heightOf defaultA rr) ∧
          IfSet
            (intLessOrEqual o4 o5)
            (Σ (T2 _) λ o6 →
              nodeSpec defaultA l d rl o6 ∧
              nodeSpec defaultA o6 rd rr result)
            (Σ (View _) λ o6 →
              viewFact defaultA o6 rl ∧
              rightDoubleConstruction defaultA o6 l d rr rd result)

  rightConstruction :
    {A : Set} → A →
    T2 A → T2 A → T1 A → T2 A → Set
  rightConstruction defaultA l r d result =
    Σ (View _) λ o3 →
      viewFact defaultA o3 r ∧
      rightConstructionFromView defaultA l d o3 result

  construction :
    {A : Set} → A →
    T2 A → T2 A → T1 A → Int → T2 A → Set
  construction defaultA l r d df result =
    IfSet
      (intLess (natToInt balancing) df)
      (leftConstruction defaultA l r d result)
      (Σ Int λ o2 →
        (o2 ≡ negateInt (natToInt balancing)) ∧
        IfSet
          (intLess df o2)
          (rightConstruction defaultA l r d result)
          (nodeSpec defaultA l d r result))

  finalConclusion :
    {A : Set} → A →
    T2 A → T2 A → T1 A → T2 A → Set
  finalConclusion defaultA l r d result =
    (seqOf defaultA result ≡
      nodeModel
        (seqOf defaultA l)
        d
        (seqOf defaultA r)) ∧
    (((zeroZ ≤Z
        subtractInt
          (addInt oneZ
            (maxInt
              (heightOf defaultA l)
              (heightOf defaultA r)))
          (heightOf defaultA result)) ∧
       (subtractInt
          (addInt oneZ
            (maxInt
              (heightOf defaultA l)
              (heightOf defaultA r)))
          (heightOf defaultA result) ≤Z oneZ)) ∧
      (heightBalance defaultA l r →
        addInt oneZ
          (maxInt
            (heightOf defaultA l)
            (heightOf defaultA r))
        ≡ heightOf defaultA result))

  balance'vc : Set₁
  balance'vc =
    (A : Set) →
    (defaultA : A) →
    (l r : T2 A) →
    (hl hr o1 : Int) →
    (d : T1 A) →
    subtractInt
      (negateInt (natToInt balancing))
      oneZ
      ≤Z subtractInt (heightOf defaultA l) (heightOf defaultA r) →
    subtractInt (heightOf defaultA l) (heightOf defaultA r)
      ≤Z addInt (natToInt balancing) oneZ →
    hl ≡ heightOf defaultA l →
    hr ≡ heightOf defaultA r →
    o1 ≡ negateInt hr →
    (o1 ≤Z subtractInt hl hr) ∧
    (subtractInt hl hr ≤Z hl) ∧
    ((df : Int) →
      df ≡ subtractInt hl hr →
      safety defaultA l r d df ∧
      ((result : T2 A) →
        construction defaultA l r d df result →
        finalConclusion defaultA l r d result))
