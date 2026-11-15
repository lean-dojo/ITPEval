-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/tree_height_HeightStack_height_stackqtvc: the verification condition
-- for computing binary-tree height with an explicit stack, including its
-- termination decrease and result invariant. This file contains no proof.

{-# OPTIONS --safe #-}

module tree_height_HeightStack_height_stackqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_
infixr 2 _∨_

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

record _×_ (A B : Set) : Set where
  constructor pair
  field
    firstComponent  : A
    secondComponent : B

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

data Tree (A : Set) : Set where
  Empty : Tree A
  Node  : Tree A → A → Tree A → Tree A

size : {A : Set} → Tree A → Int
size Empty = zeroZ
size (Node l value r) =
  addInt (addInt oneZ (size l)) (size r)

height : {A : Set} → Tree A → Int
height Empty = zeroZ
height (Node l value r) =
  addInt oneZ (maxInt (height l) (height r))

Stack : Set → Set
Stack A = List (Int × Tree A)

heights : {A : Set} → Stack A → Int
heights [] = zeroZ
heights (pair h t ∷ s') =
  maxInt (addInt h (height t)) (heights s')

sizes : {A : Set} → Stack A → Int
sizes [] = zeroZ
sizes (pair h t ∷ s') =
  addInt (size t) (sizes s')

tailMatches : {A : Set} → Stack A → Stack A → Set
tailMatches [] expected = ⊥
tailMatches (_ ∷ actualTail) expected = actualTail ≡ expected

initialObligation : {A : Set} → Int → Stack A → Set
initialObligation m [] = ⊤
initialObligation m (pair h Empty ∷ s') =
  (((zeroZ ≤Z sizes (pair h Empty ∷ s')) ∧
    (sizes s' <Z sizes (pair h Empty ∷ s'))) ∨
   ((sizes (pair h Empty ∷ s') ≡ sizes s') ∧
    tailMatches (pair h Empty ∷ s') s')) ∧
  (zeroZ ≤Z maxInt m h)
initialObligation m (pair h (Node l value r) ∷ s') =
  let current = pair h (Node l value r) ∷ s'
      next =
        pair (addInt h oneZ) l ∷
        pair (addInt h oneZ) r ∷
        s'
  in
  (((zeroZ ≤Z sizes current) ∧
    (sizes next <Z sizes current)) ∨
   ((sizes current ≡ sizes next) ∧
    tailMatches current next)) ∧
  (zeroZ ≤Z m)

resultPremise : {A : Set} → Int → Stack A → Int → Set
resultPremise m [] result =
  result ≡ m
resultPremise m (pair h Empty ∷ s') result =
  result ≡ maxInt (maxInt m h) (heights s')
resultPremise m (pair h (Node l value r) ∷ s') result =
  result ≡
    maxInt m
      (heights
        (pair (addInt h oneZ) l ∷
         pair (addInt h oneZ) r ∷
         s'))

height-stack'vc : Set₁
height-stack'vc =
  (A : Set) →
  (m : Int) →
  (s : Stack A) →
  zeroZ ≤Z m →
  initialObligation m s ∧
  ((result : Int) →
    resultPremise m s result →
    result ≡ maxInt m (heights s))
