-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/vacid_0_red_black_trees_Vacid0_removeqtvc: the remove verification
-- condition for a red-black-tree map with a default value, preserving its
-- invariant and abstract membership update. This file contains no proof.

{-# OPTIONS --safe #-}

module Vacid0RedBlackTreesVacid0RemoveQtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _<Z_
infixr 4 _×_
infixr 3 _∧_
infixr 2 _∨_
infix 2 _↔_

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

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

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

Rbt : Set
Rbt = Int × Tree

inv : Rbt → Set
inv (d , t) =
  bst t ∧ Exists Int (λ n → rbtree n t)

default : Rbt → Int
default (d , t) = d

mem : Rbt → Int → Int → Set
mem (d , t) k v =
  memt t k v ∨
  (v ≡ d ∧ ((v′ : Int) → Not (memt t k v′)))

updateSpecification : Int → Tree → Int → Tree → Set
updateSpecification m m1 k m2 =
  inv (m , m2) ∧
  ((k′ v′ : Int) →
    mem (m , m2) k′ v′ ↔
    IfSet
      (intEqual k′ k)
      (v′ ≡ m)
      (mem (m , m1) k′ v′))

remove'vc : Set
remove'vc =
  (m : Int) →
  (m1 : Tree) →
  (k : Int) →
  inv (m , m1) →
  inv (m , m1) ∧
  ((m2 : Tree) →
    updateSpecification m m1 k m2 →
    updateSpecification m m1 k m2)
