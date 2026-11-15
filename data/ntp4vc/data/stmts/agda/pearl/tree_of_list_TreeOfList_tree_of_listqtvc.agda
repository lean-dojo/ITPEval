-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/tree_of_list_TreeOfList_tree_of_listqtvc: the verification condition
-- that a binary tree built from a complete list preserves inorder traversal
-- and satisfies the stated logarithmic height bound. This file contains no proof.

{-# OPTIONS --safe #-}

module tree_of_list_TreeOfList_tree_of_listqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤Z_ _<Z_
infixr 5 _++_
infixr 3 _∧_

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

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negateInt (pos (m * suc n))
multiplyInt (negsuc m) (pos n) =
  negateInt (pos (suc m * n))
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

powerNat : Int → Nat → Int
powerNat base zero = pos (suc zero)
powerNat base (suc exponent) =
  multiplyInt base (powerNat base exponent)

powerInt : Int → Int → Int
powerInt base exponent = powerNat base (toNat exponent)

maxInt : Int → Int → Int
maxInt x y with intLess x y
... | true = y
... | false = x

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = pos (length xs)

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

zeroZ oneZ twoZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))

data Tree (A : Set) : Set where
  Empty : Tree A
  Node  : Tree A → A → Tree A → Tree A

size : {A : Set} → Tree A → Int
size Empty = zeroZ
size (Node left value right) =
  addInt (addInt oneZ (size left)) (size right)

height : {A : Set} → Tree A → Int
height Empty = zeroZ
height (Node left value right) =
  addInt oneZ (maxInt (height left) (height right))

inorder : {A : Set} → Tree A → List A
inorder Empty = []
inorder (Node left value right) =
  inorder left ++ (value ∷ inorder right)

logarithmicHeightBound : {A : Set} → Tree A → Int → Set
logarithmicHeightBound tree nodeCount =
  zeroZ <Z nodeCount →
  let h = height tree
  in
  powerInt twoZ (subtractInt h oneZ) ≤Z nodeCount
  ∧ nodeCount <Z powerInt twoZ h

tree-of-list'vc : Set₁
tree-of-list'vc =
  (A : Set) →
  (l : List A) →
  let o1 = lengthZ l
  in
  (zeroZ ≤Z o1 ∧ o1 ≤Z lengthZ l)
  ∧
  ((o2 : Tree A) →
    (o3 : List A) →
    inorder o2 ++ o3 ≡ l
    ∧ size o2 ≡ o1
    ∧ logarithmicHeightBound o2 o1 →
    inorder o2 ≡ l
    ∧ logarithmicHeightBound o2 (size o2))
