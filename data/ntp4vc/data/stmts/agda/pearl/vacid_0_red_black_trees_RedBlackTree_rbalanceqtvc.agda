-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/vacid_0_red_black_trees_RedBlackTree_rbalanceqtvc: the right-balancing
-- verification condition for binary-search and red-black tree invariants and
-- key-value membership. This file contains no proof.

{-# OPTIONS --safe #-}

module Vacid0RedBlackTreesRedBlackTreeRbalanceQtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _<Z_
infixr 3 _∧_
infixr 2 _∨_
infix 1 _↔_

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

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

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

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

oneZ : Int
oneZ = pos (suc zero)

data Color : Set where
  Red   : Color
  Black : Color

data Tree : Set where
  Leaf : Tree
  Node : Color → Tree → Int → Int → Tree → Tree

memt : Tree → Int → Int → Set
memt Leaf k v = ⊥
memt (Node color l k′ v′ r) k v =
  (k ≡ k′ ∧ v ≡ v′) ∨ memt l k v ∨ memt r k v

ltTree : Int → Tree → Set
ltTree x t =
  (k v : Int) → memt t k v → k <Z x

gtTree : Int → Tree → Set
gtTree x t =
  (k v : Int) → memt t k v → x <Z k

bst : Tree → Set
bst Leaf = ⊤
bst (Node color l k v r) =
  bst l ∧ bst r ∧ ltTree k l ∧ gtTree k r

isNotRed : Tree → Set
isNotRed Leaf = ⊤
isNotRed (Node Red l k v r) = ⊥
isNotRed (Node Black l k v r) = ⊤

rbtree : Int → Tree → Set
rbtree n Leaf = n ≡ pos zero
rbtree n (Node Red l k v r) =
  rbtree n l ∧ rbtree n r ∧ isNotRed l ∧ isNotRed r
rbtree n (Node Black l k v r) =
  rbtree (subtractInt n oneZ) l ∧
  rbtree (subtractInt n oneZ) r

almostRbtree : Int → Tree → Set
almostRbtree n Leaf = n ≡ pos zero
almostRbtree n (Node Red l k v r) =
  rbtree n l ∧ rbtree n r
almostRbtree n (Node Black l k v r) =
  rbtree (subtractInt n oneZ) l ∧
  rbtree (subtractInt n oneZ) r

rbalance : Tree → Int → Int → Tree → Tree
rbalance l k v (Node Red (Node Red b ky vy c) kz vz d) =
  Node Red
    (Node Black l k v b)
    ky vy
    (Node Black c kz vz d)
rbalance l k v (Node Red b ky vy (Node Red c kz vz d)) =
  Node Red
    (Node Black l k v b)
    ky vy
    (Node Black c kz vz d)
rbalance l k v r =
  Node Black l k v r

initialObligation : Tree → Set
initialObligation r = ⊤

resultPremise : Tree → Int → Int → Tree → Tree → Set
resultPremise l k v r result =
  result ≡ rbalance l k v r

membershipConclusion :
  Tree → Tree → Int → Int → Tree → Set
membershipConclusion l r k v result =
  (k′ v′ : Int) →
  memt result k′ v′ ↔
  IfSet
    (intEqual k′ k)
    (v′ ≡ v)
    (memt l k′ v′ ∨ memt r k′ v′)

rbalance'vc : Set
rbalance'vc =
  (k : Int) →
  (l r : Tree) →
  (v : Int) →
  ltTree k l →
  gtTree k r →
  bst l →
  bst r →
  initialObligation r ∧
  ((result : Tree) →
    resultPremise l k v r result →
    bst result ∧
    ((n : Int) →
      almostRbtree n r →
      rbtree n l →
      rbtree (addInt n oneZ) result) ∧
    membershipConclusion l r k v result)
