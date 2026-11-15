-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/binomial_heap_BinomialHeap_get_minqtvc: the binomial-heap minimum
-- verification condition for a nonempty heap-ordered forest and its
-- recursive minimum scan. This file contains no proof.

{-# OPTIONS --safe #-}

module binomial_heap_BinomialHeap_get_minqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _<Z_ _≢_
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

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : Not P → Dec P

IfDec : {P : Set} → Dec P → Set → Set → Set
IfDec (yes _) when-true when-false = when-true
IfDec (no _) when-true when-false = when-false

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

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

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

module BinomialHeapTheory
  (Elt : Set)
  (eltDefault : Elt)
  (excludedMiddle : (P : Set) → P ∨ Not P)
  (le : Elt → Elt → Set)
  (leRefl : (x : Elt) → le x x)
  (leTrans :
    (x y z : Elt) → le x y → le y z → le x z)
  (leTotal : (x y : Elt) → le x y ∨ le y x)
  where

  decide : (P : Set) → Dec P
  decide P with excludedMiddle P
  ... | left proof = yes proof
  ... | right refutation = no refutation

  data Tree : Set where
    tree : Elt → List Tree → Int → Tree

  elem : Tree → Elt
  elem (tree value descendants treeRank) = value

  leRoots : Elt → List Tree → Set
  leRoots lower [] = ⊤
  leRoots lower (t ∷ rest) =
    le lower (elem t) ∧ leRoots lower rest

  heaps : List Tree → Set
  heaps [] = ⊤
  heaps (tree root descendants treeRank ∷ rest) =
    leRoots root descendants ∧
    heaps descendants ∧
    heaps rest

  occ : Elt → List Tree → Int
  occ sought [] = zeroZ
  occ sought (tree root descendants treeRank ∷ rest)
    with decide (sought ≡ root)
  ... | yes equality =
    addInt
      (addInt oneZ (occ sought descendants))
      (occ sought rest)
  ... | no inequality =
    addInt
      (addInt zeroZ (occ sought descendants))
      (occ sought rest)

  mem : Elt → List Tree → Set
  mem sought forest = zeroZ <Z occ sought forest

  choosesMinimum : Elt → Elt → Elt → Set
  choosesMinimum x m choice =
    IfDec
      (decide (le x m))
      (choice ≡ x)
      (choice ≡ m)

  tailMatches : List Tree → List Tree → Set
  tailMatches [] expectedTail = ⊥
  tailMatches (head ∷ actualTail) expectedTail =
    actualTail ≡ expectedTail

  scanSafety : Elt → List Tree → Set
  scanSafety m [] = ⊤
  scanSafety m (tree x descendants treeRank ∷ rest) =
    (choice : Elt) →
    choosesMinimum x m choice →
    tailMatches (tree x descendants treeRank ∷ rest) rest ∧
    heaps rest

  scanResultPremise : Elt → Elt → List Tree → Set
  scanResultPremise m result [] = result ≡ m
  scanResultPremise
    m
    result
    (tree x descendants treeRank ∷ rest) =
      Exists Elt λ choice →
        choosesMinimum x m choice ∧
        (result ≡ choice ∨ mem result rest) ∧
        le result choice ∧
        ((x₁ : Elt) → mem x₁ rest → le result x₁)

  scanResultConclusion : Elt → Elt → List Tree → Set
  scanResultConclusion m result forest =
    (result ≡ m ∨ mem result forest) ∧
    le result m ∧
    ((x : Elt) → mem x forest → le result x)

  scanObligation : Elt → List Tree → Set
  scanObligation m forest =
    scanSafety m forest ∧
    ((result : Elt) →
      scanResultPremise m result forest →
      scanResultConclusion m result forest)

  nonemptyHeadCase : List Tree → Set
  nonemptyHeadCase [] = ⊥
  nonemptyHeadCase (t ∷ rest) =
    ((m : Elt) →
      (forest : List Tree) →
      heaps forest →
      scanObligation m forest) ∧
    heaps rest

  finalResultPremise : Elt → List Tree → Set
  finalResultPremise result [] = ⊥
  finalResultPremise result (t ∷ rest) =
    (result ≡ elem t ∨ mem result rest) ∧
    le result (elem t) ∧
    ((x : Elt) → mem x rest → le result x)

  finalResultConclusion : Elt → List Tree → Set
  finalResultConclusion result forest =
    mem result forest ∧
    ((x : Elt) → mem x forest → le result x)

  get-min'vc : Set
  get-min'vc =
    (h : List Tree) →
    heaps h →
    h ≢ [] →
    nonemptyHeadCase h ∧
    ((result : Elt) →
      finalResultPremise result h →
      finalResultConclusion result h)
