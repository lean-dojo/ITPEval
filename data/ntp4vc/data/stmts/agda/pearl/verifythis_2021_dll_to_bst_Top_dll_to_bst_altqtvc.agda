-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2021_dll_to_bst_Top_dll_to_bst_altqtvc: the verification
-- condition for converting a finite-map doubly linked list into an
-- inorder-preserving balanced binary tree. This file contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2021DllToBstTopDllToBstAltVC where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤Z_ _<Z_ _≢_ _∈_
infixr 5 _++_
infixr 3 _∧_
infix 2 _↔_

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

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

data _∈_ {A : Set} (x : A) : List A → Set where
  here  : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

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

maxInt : Int → Int → Int
maxInt x y with intLess x y
... | true = y
... | false = x

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

powerNat : Int → Nat → Int
powerNat base zero = pos (suc zero)
powerNat base (suc exponent) =
  multiplyInt base (powerNat base exponent)

powerInt : Int → Int → Int
powerInt base exponent = powerNat base (toNat exponent)

zeroZ oneZ twoZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = pos (length xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

ifValue : {A : Set} → Bool → A → A → A
ifValue true when-true when-false = when-true
ifValue false when-true when-false = when-false

record FiniteMap (A : Set) : Set where
  constructor finiteMap
  field
    keys     : List A
    contents : A → A

open FiniteMap

domainEqual : {A : Set} → FiniteMap A → FiniteMap A → Set
domainEqual {A = A} leftMap rightMap =
  (key : A) → (key ∈ keys leftMap) ↔ (key ∈ keys rightMap)

record Signature : Set₁ where
  field
    Loc          : Set
    null         : Loc
    Store        : Set
    storeDefault : Store
    toFMap       : Store → FiniteMap Loc

open Signature

nthLoc :
  (sig : Signature) →
  List (Loc sig) →
  Int →
  Loc sig
nthLoc sig xs index =
  nthDefault (null sig) (toNat index) xs

valid :
  (sig : Signature) →
  FiniteMap (Loc sig) →
  FiniteMap (Loc sig) →
  List (Loc sig) →
  Set
valid sig prev next s =
  (i : Int) →
  (zeroZ ≤Z i ∧ i <Z lengthZ s) →
  nthLoc sig s i ≢ null sig
  ∧ nthLoc sig s i ∈ keys prev
  ∧ nthLoc sig s i ∈ keys next
  ∧ ((j : Int) →
      (i <Z j ∧ j <Z lengthZ s) →
      nthLoc sig s i ≢ nthLoc sig s j)

dll :
  (sig : Signature) →
  FiniteMap (Loc sig) →
  FiniteMap (Loc sig) →
  List (Loc sig) →
  Loc sig →
  Int →
  Int →
  Set
dll sig prev next s head lo hi =
  valid sig prev next s
  ∧ (zeroZ ≤Z lo ∧ lo ≤Z hi ∧ hi ≤Z lengthZ s)
  ∧ head ≡
      ifValue
        (intEqual lo (lengthZ s))
        (null sig)
        (nthLoc sig s lo)
  ∧ ((i : Int) →
      (lo ≤Z i ∧ i <Z subtractInt hi oneZ) →
      contents next (nthLoc sig s i) ≡
        nthLoc sig s (addInt i oneZ))
  ∧ ((i : Int) →
      (lo <Z i ∧ i <Z hi) →
      contents prev (nthLoc sig s i) ≡
        nthLoc sig s (subtractInt i oneZ))
  ∧ (lo <Z hi →
      contents next
        (nthLoc sig s (subtractInt hi oneZ))
      ≡ ifValue
          (intEqual hi (lengthZ s))
          (null sig)
          (nthLoc sig s hi))
  ∧ (lo <Z hi →
      contents prev (nthLoc sig s lo)
      ≡ ifValue
          (intEqual lo zeroZ)
          (null sig)
          (nthLoc sig s (subtractInt lo oneZ)))

data Tree : Set where
  Empty : Tree
  Node  : Tree → Int → Tree → Tree

size : Tree → Int
size Empty = zeroZ
size (Node left position right) =
  addInt (addInt oneZ (size left)) (size right)

height : Tree → Int
height Empty = zeroZ
height (Node left position right) =
  addInt oneZ (maxInt (height left) (height right))

tree :
  (sig : Signature) →
  FiniteMap (Loc sig) →
  FiniteMap (Loc sig) →
  List (Loc sig) →
  Loc sig →
  Tree →
  Int →
  Int →
  Set
tree sig prev next s root Empty lo hi =
  valid sig prev next s
  ∧ (zeroZ ≤Z lo ∧ lo ≤Z hi ∧ hi ≤Z lengthZ s)
  ∧ (root ≡ null sig ∧ lo ≡ hi)
tree sig prev next s root (Node left position right) lo hi =
  valid sig prev next s
  ∧ (zeroZ ≤Z lo ∧ lo ≤Z hi ∧ hi ≤Z lengthZ s)
  ∧ (lo ≤Z position ∧ position <Z hi)
  ∧ root ≡ nthLoc sig s position
  ∧ tree
      sig
      prev
      next
      s
      (contents prev root)
      left
      lo
      position
  ∧ tree
      sig
      prev
      next
      s
      (contents next root)
      right
      (addInt position oneZ)
      hi

inorder :
  (sig : Signature) →
  List (Loc sig) →
  Tree →
  List (Loc sig)
inorder sig s Empty = []
inorder sig s (Node left position right) =
  inorder sig s left
  ++ (nthLoc sig s position ∷ inorder sig s right)

lookupAgreement :
  (sig : Signature) →
  FiniteMap (Loc sig) →
  FiniteMap (Loc sig) →
  List (Loc sig) →
  Int →
  Int →
  Set
lookupAgreement sig current original s lower upper =
  (i : Int) →
  (lower ≤Z i ∧ i <Z upper) →
  contents current (nthLoc sig s i) ≡
    contents original (nthLoc sig s i)

heightBound : Tree → Int → Set
heightBound result n =
  let h = height result
  in
  powerInt twoZ (subtractInt h oneZ) ≤Z n
  ∧ n <Z powerInt twoZ h

finalResult :
  (sig : Signature) →
  FiniteMap (Loc sig) →
  FiniteMap (Loc sig) →
  List (Loc sig) →
  Loc sig →
  Tree →
  Set
finalResult sig prev next s root result =
  tree sig prev next s root result zeroZ (lengthZ s)
  ∧ size result ≡ lengthZ s
  ∧ inorder sig s result ≡ s
  ∧ (zeroZ <Z lengthZ s →
      heightBound result (lengthZ s))

recursiveCallVC :
  (sig : Signature) →
  Store sig →
  Store sig →
  List (Loc sig) →
  Int →
  Store sig →
  Store sig →
  Loc sig →
  Tree →
  Set
recursiveCallVC sig prev next s n next₁ prev₁ root result =
  (tree
    sig
    (toFMap sig prev₁)
    (toFMap sig next₁)
    s
    root
    result
    zeroZ
    (addInt zeroZ n)
  ∧ domainEqual (toFMap sig prev₁) (toFMap sig prev)
  ∧ domainEqual (toFMap sig next₁) (toFMap sig next)
  ∧ lookupAgreement
      sig
      (toFMap sig prev₁)
      (toFMap sig prev)
      s
      zeroZ
      zeroZ
  ∧ lookupAgreement
      sig
      (toFMap sig prev₁)
      (toFMap sig prev)
      s
      (addInt zeroZ n)
      (lengthZ s)
  ∧ lookupAgreement
      sig
      (toFMap sig next₁)
      (toFMap sig next)
      s
      zeroZ
      zeroZ
  ∧ lookupAgreement
      sig
      (toFMap sig next₁)
      (toFMap sig next)
      s
      (addInt zeroZ n)
      (lengthZ s)
  ∧ (zeroZ <Z n → heightBound result n))
  →
  finalResult
    sig
    (toFMap sig prev₁)
    (toFMap sig next₁)
    s
    root
    result

dll-to-bst-alt'vc : Set₁
dll-to-bst-alt'vc =
  (sig : Signature) →
  (prev : Store sig) →
  (next : Store sig) →
  (s : List (Loc sig)) →
  (head : Loc sig) →
  dll
    sig
    (toFMap sig prev)
    (toFMap sig next)
    s
    head
    zeroZ
    (lengthZ s)
  →
  dll
    sig
    (toFMap sig prev)
    (toFMap sig next)
    s
    head
    zeroZ
    (lengthZ s)
  ∧
  let n = lengthZ s
  in
  dll
    sig
    (toFMap sig prev)
    (toFMap sig next)
    s
    head
    zeroZ
    (addInt zeroZ n)
  ∧ ((next₁ : Store sig) →
     (prev₁ : Store sig) →
     (root : Loc sig) →
     (result : Tree) →
     recursiveCallVC
       sig
       prev
       next
       s
       n
       next₁
       prev₁
       root
       result)
