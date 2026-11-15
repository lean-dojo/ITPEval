-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/vstte12_tree_reconstruction_ZipperBased_buildqtvc: the initial
-- zipper-state invariant and the soundness and failure conditions for
-- reconstructing a binary tree from its leaf-depth list. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module vstte12_tree_reconstruction_ZipperBased_buildqtvc where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infixr 5 _++_
infixr 3 _∧_

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

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ (x ∷ [])

data Tree : Set where
  Leaf : Tree
  Node : Tree → Tree → Tree

depths : Int → Tree → List Int
depths d Leaf = d ∷ []
depths d (Node left right) =
  depths (addInt d oneZ) left ++
  depths (addInt d oneZ) right

record Entry : Set where
  constructor entry
  field
    entryDepth : Int
    entryTree  : Tree

forestDepths : List Entry → List Int
forestDepths [] = []
forestDepths (entry d tree ∷ rest) =
  depths d tree ++ forestDepths rest

greedy : Int → Int → Tree → Set
greedy d d1 Leaf =
  Not (d ≡ d1) ∧ ⊤
greedy d d1 (Node left right) =
  Not (d ≡ d1) ∧ greedy d (addInt d1 oneZ) left

data G : List Entry → Set where
  Gnil : G []
  Gone : (d : Int) → (tree : Tree) →
    G (entry d tree ∷ [])
  Gtwo :
    (d1 d2 : Int) →
    (tree2 tree1 : Tree) →
    (rest : List Entry) →
    greedy d1 d2 tree2 →
    G (entry d1 tree1 ∷ rest) →
    G (entry d2 tree2 ∷ entry d1 tree1 ∷ rest)

onlyLeaf : List Entry → Set
onlyLeaf [] = ⊤
onlyLeaf (entry d tree ∷ rest) =
  tree ≡ Leaf ∧ onlyLeaf rest

mapLeaf : List Int → List Entry
mapLeaf [] = []
mapLeaf (d ∷ rest) = entry d Leaf ∷ mapLeaf rest

headInvariant : Int → Tree → List Entry → Set
headInvariant d2 Leaf left = ⊤
headInvariant d2 (Node leftSubtree rightSubtree) left =
  G (entry (addInt d2 oneZ) leftSubtree ∷ left)

rightInvariant : List Entry → List Entry → Set
rightInvariant [] left = ⊤
rightInvariant (entry d2 tree2 ∷ rightRest) left =
  onlyLeaf rightRest ∧ headInvariant d2 tree2 left

build'vc : Set
build'vc =
  (s : List Int) →
  let o1 : List Entry
      o1 = mapLeaf s
      o2 : List Entry
      o2 = []
  in
  (G o2 ∧ rightInvariant o1 o2) ∧
  ((result : Tree) →
    depths zeroZ result ≡ forestDepths (reverse o2 ++ o1) →
    depths zeroZ result ≡ s) ∧
  (((tree : Tree) →
    Not (depths zeroZ tree ≡ forestDepths (reverse o2 ++ o1))) →
    ((tree : Tree) →
      Not (depths zeroZ tree ≡ s)))
