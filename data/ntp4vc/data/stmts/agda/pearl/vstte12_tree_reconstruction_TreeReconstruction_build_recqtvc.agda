-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/vstte12_tree_reconstruction_TreeReconstruction_build_recqtvc: the
-- recursive verification condition for reconstructing a binary tree from its
-- left-to-right list of leaf depths. This file contains no proof.

{-# OPTIONS --safe #-}

module vstte12_tree_reconstruction_TreeReconstruction_build_recqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_ _<N_
infixr 5 _++_
infixr 3 _∧_
infixr 2 _∨_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  or-left  : A → A ∨ B
  or-right : B → A ∨ B

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

_<N_ : Nat → Nat → Set
m <N n = natLess m n ≡ true

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

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = pos (length xs)

headDefault : {A : Set} → A → List A → A
headDefault default [] = default
headDefault default (x ∷ xs) = x

headInt : List Int → Int
headInt = headDefault zeroZ

data Tree : Set where
  Leaf : Tree
  Node : Tree → Tree → Tree

depths : Int → Tree → List Int
depths d Leaf = d ∷ []
depths d (Node left right) =
  depths (addInt d oneZ) left ++
  depths (addInt d oneZ) right

NoDecomposition : Int → List Int → Set
NoDecomposition d source =
  (tree : Tree) →
  (suffix : List Int) →
  Not (depths d tree ++ suffix ≡ source)

FirstCallVariant : List Int → Int → Set
FirstCallVariant source d =
  let next-depth = addInt d oneZ
      measure = subtractInt (headInt source) d
  in
  zeroZ ≤Z measure ∧
  subtractInt (headInt source) next-depth <Z measure

SecondCallVariant : List Int → Int → List Int → Set
SecondCallVariant source d remainder =
  let next-depth = addInt d oneZ
      measure = subtractInt (headInt source) d
  in
  (zeroZ ≤Z lengthZ source ∧
   length remainder <N length source)
  ∨
  (length source ≡ length remainder ∧
   zeroZ ≤Z measure ∧
   subtractInt (headInt remainder) next-depth <Z measure)

AfterFirstSuccess :
  List Int → Int → Tree → List Int → Set
AfterFirstSuccess source d left-tree remainder =
  let next-depth = addInt d oneZ
  in
  SecondCallVariant source d remainder ∧
  ((right-tree : Tree) →
   (final-suffix : List Int) →
   remainder ≡ depths next-depth right-tree ++ final-suffix →
   source ≡ depths d (Node left-tree right-tree) ++ final-suffix)
  ∧
  (NoDecomposition next-depth remainder →
   NoDecomposition d source)

RecursiveCase : List Int → Int → Set
RecursiveCase source d =
  let next-depth = addInt d oneZ
  in
  FirstCallVariant source d ∧
  ((left-tree : Tree) →
   (remainder : List Int) →
   source ≡ depths next-depth left-tree ++ remainder →
   AfterFirstSuccess source d left-tree remainder)
  ∧
  (NoDecomposition next-depth source →
   NoDecomposition d source)

BuildRecCondition : List Int → Int → Set
BuildRecCondition [] d =
  NoDecomposition d []
BuildRecCondition (h ∷ tail) d =
  IfSet
    (intLess h d)
    (NoDecomposition d (h ∷ tail))
    (IfSet
      (intEqual h d)
      ((h ∷ tail) ≡ depths d Leaf ++ tail)
      (RecursiveCase (h ∷ tail) d))

build-rec'vc : Set
build-rec'vc =
  (source : List Int) →
  (depth : Int) →
  BuildRecCondition source depth
