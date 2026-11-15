-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/mergesort_list_OCamlMergesort_rev_sortqtvc: the reverse-order list
-- mergesort verification condition, including base-case results, recursive
-- call bounds, sortedness, and permutation preservation. This file contains no proof.

{-# OPTIONS --safe #-}

module mergesort_list_OCamlMergesort_rev_sortqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_ _∈_
infixr 5 _++_
infixr 3 _∧_
infixr 2 _∨_
infix 1 _↔_

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

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

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : Not P → Dec P

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

IfDec : {P : Set} → Dec P → Set → Set → Set
IfDec (yes _) when-true when-false = when-true
IfDec (no _) when-true when-false = when-false

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

halfNat : Nat → Nat
halfNat zero = zero
halfNat (suc zero) = zero
halfNat (suc (suc n)) = suc (halfNat n)

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

-- Signed division by two truncated toward zero. Under the VC hypothesis
-- 2 ≤ n, this is exactly Why3 integer division by two.
tdivTwo : Int → Int
tdivTwo (pos n) = pos (halfNat n)
tdivTwo (negsuc n) = negative (halfNat (suc n))

zeroZ oneZ twoZ threeZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))
threeZ = pos (suc (suc (suc zero)))

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = pos (length xs)

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

reverseAcc : {A : Set} → List A → List A → List A
reverseAcc [] acc = acc
reverseAcc (x ∷ xs) acc = reverseAcc xs (x ∷ acc)

reverse : {A : Set} → List A → List A
reverse xs = reverseAcc xs []

data _∈_ {A : Set} (x : A) : List A → Set where
  here :
    {xs : List A} →
    x ∈ (x ∷ xs)

  there :
    {y : A} {xs : List A} →
    x ∈ xs →
    x ∈ (y ∷ xs)

data Perm {A : Set} : List A → List A → Set where
  permNil :
    Perm [] []

  permKeep :
    {x : A} {xs ys : List A} →
    Perm xs ys →
    Perm (x ∷ xs) (x ∷ ys)

  permSwap :
    (x y : A) →
    (xs : List A) →
    Perm (x ∷ y ∷ xs) (y ∷ x ∷ xs)

  permTrans :
    {xs ys zs : List A} →
    Perm xs ys →
    Perm ys zs →
    Perm xs zs

data Sorted {A : Set} (le : A → A → Set) : List A → Set where
  sortedNil :
    Sorted le []

  sortedOne :
    (x : A) →
    Sorted le (x ∷ [])

  sortedTwo :
    (x y : A) →
    (xs : List A) →
    le x y →
    Sorted le (y ∷ xs) →
    Sorted le (x ∷ y ∷ xs)

record MergesortModel (Elt : Set) : Set₁ where
  field
    eltDefault : Elt

    excludedMiddle :
      (P : Set) →
      P ∨ Not P

    le : Elt → Elt → Set
    leRefl :
      (x : Elt) →
      le x x
    leTrans :
      (x y z : Elt) →
      le x y →
      le y z →
      le x z
    leTotal :
      (x y : Elt) →
      le x y ∨ le y x

    sortedMem :
      (xs : List Elt) →
      (x : Elt) →
      (((y : Elt) → y ∈ xs → le x y) ∧ Sorted le xs)
        ↔ Sorted le (x ∷ xs)

    sortedAppend :
      (xs ys : List Elt) →
      (Sorted le xs ∧
       Sorted le ys ∧
       ((x y : Elt) → x ∈ xs → y ∈ ys → le x y))
        ↔ Sorted le (xs ++ ys)

    prefix1 :
      {A : Set} →
      A →
      Int →
      List A →
      List A

    prefixDefZero :
      {A : Set} →
      (default : A) →
      (xs : List A) →
      prefix1 default zeroZ xs ≡ []

    prefixDefConsPositive :
      {A : Set} →
      (default : A) →
      (n : Int) →
      (x : A) →
      (xs : List A) →
      zeroZ <Z n →
      prefix1 default n (x ∷ xs) ≡
        x ∷ prefix1 default (subtractInt n oneZ) xs

open MergesortModel

decide :
  {Elt : Set} →
  MergesortModel Elt →
  (P : Set) →
  Dec P
decide model P with excludedMiddle model P
... | left proof = yes proof
... | right refutation = no refutation

TwoElementShape : {A : Set} → List A → Set
TwoElementShape [] = ⊥
TwoElementShape (_ ∷ []) = ⊥
TwoElementShape (_ ∷ _ ∷ _) = ⊤

ThreeElementShape : {A : Set} → List A → Set
ThreeElementShape [] = ⊥
ThreeElementShape (_ ∷ []) = ⊥
ThreeElementShape (_ ∷ _ ∷ []) = ⊥
ThreeElementShape (_ ∷ _ ∷ _ ∷ _) = ⊤

EmptyAccumulatorConditions :
  {Elt : Set} →
  MergesortModel Elt →
  List Elt →
  List Elt →
  Set
EmptyAccumulatorConditions {Elt} model s1 s2 =
  (Sorted (le model) (reverse []) ∧
   Sorted (le model) s1 ∧
   Sorted (le model) s2)
  ∧ ((x y : Elt) →
      x ∈ [] →
      y ∈ s1 →
      le model x y)
  ∧ ((x y : Elt) →
      x ∈ [] →
      y ∈ s2 →
      le model x y)

SecondSortContinuation :
  {Elt : Set} →
  MergesortModel Elt →
  Int →
  List Elt →
  List Elt →
  Set
SecondSortContinuation model n2 l2 s1 =
  (s2 : List _) →
  (Sorted (le model) s2 ∧
   Perm s2 (prefix1 model (eltDefault model) n2 l2)) →
  EmptyAccumulatorConditions model s1 s2

SecondRecursiveCall :
  {Elt : Set} →
  MergesortModel Elt →
  Int →
  Int →
  List Elt →
  List Elt →
  Set
SecondRecursiveCall model n n2 l2 s1 =
  (((zeroZ ≤Z n) ∧ (n2 <Z n)) ∧
   (twoZ ≤Z n2) ∧
   (n2 ≤Z lengthZ l2))
  ∧ SecondSortContinuation model n2 l2 s1

FirstSortContinuation :
  {Elt : Set} →
  MergesortModel Elt →
  Int →
  Int →
  Int →
  List Elt →
  List Elt →
  Set
FirstSortContinuation model n n1 n2 l l2 =
  (s1 : List _) →
  (Sorted (le model) s1 ∧
   Perm s1 (prefix1 model (eltDefault model) n1 l)) →
  SecondRecursiveCall model n n2 l2 s1

FirstRecursiveCall :
  {Elt : Set} →
  MergesortModel Elt →
  Int →
  Int →
  Int →
  List Elt →
  List Elt →
  Set
FirstRecursiveCall model n n1 n2 l l2 =
  (((zeroZ ≤Z n) ∧ (n1 <Z n)) ∧
   (twoZ ≤Z n1) ∧
   (n1 ≤Z lengthZ l))
  ∧ FirstSortContinuation model n n1 n2 l l2

SplitContinuation :
  {Elt : Set} →
  MergesortModel Elt →
  Int →
  Int →
  Int →
  List Elt →
  Set
SplitContinuation model n n1 n2 l =
  (l2 : List _) →
  l ≡ prefix1 model (eltDefault model) n1 l ++ l2 →
  FirstRecursiveCall model n n1 n2 l l2

RecursiveCallObligations :
  {Elt : Set} →
  MergesortModel Elt →
  Int →
  List Elt →
  Set
RecursiveCallObligations model n l =
  let n1 = tdivTwo n
      n2 = subtractInt n n1
  in
  ((zeroZ ≤Z n1) ∧ (n1 ≤Z lengthZ l))
  ∧ SplitContinuation model n n1 n2 l

InitialObligation :
  {Elt : Set} →
  MergesortModel Elt →
  Int →
  List Elt →
  Set
InitialObligation model n l =
  IfSet
    (intEqual n twoZ)
    (TwoElementShape l)
    (IfSet
      (intEqual n threeZ)
      (ThreeElementShape l)
      (Not (twoZ ≡ zeroZ) ∧
       RecursiveCallObligations model n l))

TwoElementResult :
  {Elt : Set} →
  MergesortModel Elt →
  List Elt →
  List Elt →
  Set
TwoElementResult model [] result = ⊥
TwoElementResult model (_ ∷ []) result = ⊥
TwoElementResult model (x1 ∷ x2 ∷ _) result =
  IfDec
    (decide model (Not (le model x1 x2)))
    (result ≡ x1 ∷ x2 ∷ [])
    (result ≡ x2 ∷ x1 ∷ [])

ThreeElementResult :
  {Elt : Set} →
  MergesortModel Elt →
  List Elt →
  List Elt →
  Set
ThreeElementResult model [] result = ⊥
ThreeElementResult model (_ ∷ []) result = ⊥
ThreeElementResult model (_ ∷ _ ∷ []) result = ⊥
ThreeElementResult model (x1 ∷ x2 ∷ x3 ∷ _) result =
  IfDec
    (decide model (Not (le model x1 x2)))
    (IfDec
      (decide model (Not (le model x2 x3)))
      (result ≡ x1 ∷ x2 ∷ x3 ∷ [])
      (IfDec
        (decide model (Not (le model x1 x3)))
        (result ≡ x1 ∷ x3 ∷ x2 ∷ [])
        (result ≡ x3 ∷ x1 ∷ x2 ∷ [])))
    (IfDec
      (decide model (Not (le model x1 x3)))
      (result ≡ x2 ∷ x1 ∷ x3 ∷ [])
      (IfDec
        (decide model (Not (le model x2 x3)))
        (result ≡ x2 ∷ x3 ∷ x1 ∷ [])
        (result ≡ x3 ∷ x2 ∷ x1 ∷ [])))

RecursiveResultPremise :
  {Elt : Set} →
  MergesortModel Elt →
  Int →
  List Elt →
  List Elt →
  Set
RecursiveResultPremise {Elt} model n l result =
  let n1 = tdivTwo n
  in
  Exists (List Elt) λ l2 →
    l ≡ prefix1 model (eltDefault model) n1 l ++ l2
    ∧ Exists (List Elt) λ s1 →
      (Sorted (le model) s1 ∧
       Perm s1 (prefix1 model (eltDefault model) n1 l))
      ∧ Exists (List Elt) λ s2 →
        (Sorted (le model) s2 ∧
         Perm s2
           (prefix1 model
             (eltDefault model)
             (subtractInt n n1)
             l2))
        ∧ Sorted (le model) (reverse result)
        ∧ Perm result (([] ++ s1) ++ s2)

ResultPremise :
  {Elt : Set} →
  MergesortModel Elt →
  Int →
  List Elt →
  List Elt →
  Set
ResultPremise model n l result =
  IfSet
    (intEqual n twoZ)
    (TwoElementResult model l result)
    (IfSet
      (intEqual n threeZ)
      (ThreeElementResult model l result)
      (RecursiveResultPremise model n l result))

ResultConclusion :
  {Elt : Set} →
  MergesortModel Elt →
  Int →
  List Elt →
  Set
ResultConclusion {Elt} model n l =
  (result : List Elt) →
  ResultPremise model n l result →
  Sorted (le model) (reverse result)
  ∧ Perm result (prefix1 model (eltDefault model) n l)

RevSortVC :
  {Elt : Set} →
  MergesortModel Elt →
  Int →
  List Elt →
  Set
RevSortVC model n l =
  InitialObligation model n l
  ∧ ResultConclusion model n l

rev-sort'vc : Set₁
rev-sort'vc =
  (Elt : Set) →
  (model : MergesortModel Elt) →
  (n : Int) →
  (l : List Elt) →
  twoZ ≤Z n →
  n ≤Z lengthZ l →
  RevSortVC model n l
