-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/foveoos11_challenge2_MaximumTree_maximumqtvc: a verification condition
-- for computing the maximum of a binary tree of integers, including recursive
-- size-decrease obligations and a greatest-element postcondition. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module foveoos11_challenge2_MaximumTree_maximumqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_ _≢_
infixr 3 _∧_
infixr 2 _∨_

data ⊤ : Set where
  tt : ⊤

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

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

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

maxInt : Int → Int → Int
maxInt x y with intLess x y
... | true = y
... | false = x

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

data Tree : Set where
  Empty : Tree
  Node  : Tree → Int → Tree → Tree

size : Tree → Int
size Empty = zeroZ
size (Node l value r) =
  addInt (addInt oneZ (size l)) (size r)

mem : Int → Tree → Set
mem sought Empty = ⊥
mem sought (Node l value r) =
  mem sought l ∨ sought ≡ value ∨ mem sought r

maximumAt : Int → Tree → Set
maximumAt candidate subtree =
  mem candidate subtree ∧
  ((x : Int) → mem x subtree → x ≤Z candidate)

structuralCondition : Tree → Set
structuralCondition Empty = ⊥
structuralCondition (Node Empty value Empty) = ⊤
structuralCondition
  whole@(Node Empty value subtree@(Node _ _ _)) =
    (zeroZ ≤Z size whole ∧ size subtree <Z size whole) ∧
    subtree ≢ Empty
structuralCondition
  whole@(Node subtree@(Node _ _ _) value Empty) =
    (zeroZ ≤Z size whole ∧ size subtree <Z size whole) ∧
    subtree ≢ Empty
structuralCondition
  whole@(Node leftTree@(Node _ _ _) value rightTree@(Node _ _ _)) =
    ((zeroZ ≤Z size whole ∧ size rightTree <Z size whole) ∧
     rightTree ≢ Empty) ∧
    ((rightMaximum : Int) →
      maximumAt rightMaximum rightTree →
      (zeroZ ≤Z size whole ∧ size leftTree <Z size whole) ∧
      leftTree ≢ Empty)

resultPremise : Tree → Int → Set
resultPremise Empty result = ⊥
resultPremise (Node Empty value Empty) result =
  result ≡ value
resultPremise
  (Node Empty value subtree@(Node _ _ _))
  result =
    Exists Int λ subtreeMaximum →
      maximumAt subtreeMaximum subtree ∧
      result ≡ maxInt subtreeMaximum value
resultPremise
  (Node subtree@(Node _ _ _) value Empty)
  result =
    Exists Int λ subtreeMaximum →
      maximumAt subtreeMaximum subtree ∧
      result ≡ maxInt subtreeMaximum value
resultPremise
  (Node leftTree@(Node _ _ _) value rightTree@(Node _ _ _))
  result =
    Exists Int λ rightMaximum →
      maximumAt rightMaximum rightTree ∧
      Exists Int λ leftMaximum →
        maximumAt leftMaximum leftTree ∧
        result ≡ maxInt leftMaximum (maxInt value rightMaximum)

resultConclusion : Tree → Int → Set
resultConclusion tree result =
  mem result tree ∧
  ((x : Int) → mem x tree → x ≤Z result)

maximum'vc : Set
maximum'vc =
  (tree : Tree) →
  tree ≢ Empty →
  structuralCondition tree ∧
  ((result : Int) →
    resultPremise tree result →
    resultConclusion tree result)
