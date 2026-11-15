-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/avl/avl_AVL_front_nodeqtvc: an AVL-tree view verification condition
-- relating cached heights and sequences to the initial element of a node.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module avl_AVL_front_nodeqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
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

  Fact0 :
    {A : Set} → (defaultA : A) →
    View A → T2 A → Set
  Fact0 defaultA AEmpty l =
    (hgt (m1 defaultA l) ≡ zeroZ) ∧
    (seq (m1 defaultA l) ≡ [])
  Fact0 defaultA (ANode left datum right height summary) l =
    (seq (m1 defaultA l) ≡
      nodeModel
        (seq (m1 defaultA left))
        datum
        (seq (m1 defaultA right))) ∧
    (summary ≡
      agg (t1Default defaultA)
        (measureClosure defaultA)
        (seq (m1 defaultA l))) ∧
    ((negateInt (natToInt balancing) ≤Z
        subtractInt
          (hgt (m1 defaultA left))
          (hgt (m1 defaultA right))) ∧
     (subtractInt
        (hgt (m1 defaultA left))
        (hgt (m1 defaultA right)) ≤Z
          natToInt balancing)) ∧
    (hgt (m1 defaultA l) ≡ natToInt height) ∧
    (natToInt height ≡
      addInt oneZ
        (maxInt
          (hgt (m1 defaultA left))
          (hgt (m1 defaultA right))))

  HeightConclusion :
    {A : Set} → (defaultA : A) →
    View A → T2 A → Set
  HeightConclusion defaultA AEmpty l = ⊤
  HeightConclusion defaultA (ANode left _ _ _ _) l =
    (zeroZ ≤Z hgt (m1 defaultA l)) ∧
    (hgt (m1 defaultA left) <Z hgt (m1 defaultA l))

  ViewResult :
    {A : Set} → (defaultA : A) →
    View A → T1 A → T1 A → Set
  ViewResult defaultA AEmpty datum result =
    result ≡ datum
  ViewResult defaultA (ANode left datum _ _ _) _ result =
    result ≡
      nthDefault
        (t1Default defaultA)
        zero
        (append (seq (m1 defaultA left)) (datum ∷ []))

  NodeResult :
    {A : Set} → (defaultA : A) →
    T2 A → T1 A → T1 A → Set
  NodeResult defaultA l datum result =
    result ≡
      nthDefault
        (t1Default defaultA)
        zero
        (append (seq (m1 defaultA l)) (datum ∷ []))

  front-node'vc : Set₁
  front-node'vc =
    (A : Set) →
    (defaultA : A) →
    (o1 : View A) →
    (l : T2 A) →
    (datum : T1 A) →
    Fact0 defaultA o1 l →
    HeightConclusion defaultA o1 l ∧
    ((result : T1 A) →
      ViewResult defaultA o1 datum result →
      NodeResult defaultA l datum result)
