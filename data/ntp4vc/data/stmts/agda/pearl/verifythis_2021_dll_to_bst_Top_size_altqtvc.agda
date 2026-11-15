-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2021_dll_to_bst_Top_size_altqtvc: the loop verification
-- condition for counting the nodes of a finite-map doubly linked list using
-- a preserved suffix invariant and a decreasing integer variant. This file contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2021DllToBstTopSizeAltVC where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_ _≢_ _∈_
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

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

ifValue : {A : Set} → Bool → A → A → A
ifValue true when-true when-false = when-true
ifValue false when-true when-false = when-false

notBool : Bool → Bool
notBool true = false
notBool false = true

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

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

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

record FiniteMap (A : Set) : Set where
  constructor finiteMap
  field
    keys     : List A
    contents : A → A

open FiniteMap

record Signature : Set₁ where
  field
    Loc              : Set
    null             : Loc
    locEqual         : Loc → Loc → Bool
    locEqual-correct :
      (left right : Loc) →
      (locEqual left right ≡ true) ↔ (left ≡ right)
    Store            : Set
    toFMap           : Store → FiniteMap Loc

open Signature

nthLoc :
  (sig : Signature) →
  List (Loc sig) →
  Int →
  Loc sig
nthLoc sig xs index =
  nthDefault (null sig) (toNat index) xs

nodeAt :
  (sig : Signature) →
  List (Loc sig) →
  Int →
  Loc sig
nodeAt sig s index =
  ifValue
    (intEqual index (lengthZ s))
    (null sig)
    (nthLoc sig s index)

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
  ∧ head ≡ nodeAt sig s lo
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
      ≡ nodeAt sig s hi)
  ∧ (lo <Z hi →
      contents prev (nthLoc sig s lo)
      ≡ ifValue
          (intEqual lo zeroZ)
          (null sig)
          (nthLoc sig s (subtractInt lo oneZ)))

loopObligation :
  (sig : Signature) →
  FiniteMap (Loc sig) →
  FiniteMap (Loc sig) →
  List (Loc sig) →
  Int →
  Loc sig →
  Set
loopObligation sig prev next s len p =
  IfSet
    (notBool (locEqual sig p (null sig)))
    (p ∈ keys next
     ∧
     let o₁ = contents next p
     in
     o₁ ≡ contents next p →
     ((zeroZ ≤Z subtractInt (lengthZ s) len
       ∧ subtractInt (lengthZ s) (addInt len oneZ)
           <Z subtractInt (lengthZ s) len)
      ∧ dll
          sig
          prev
          next
          s
          o₁
          (addInt len oneZ)
          (lengthZ s)))
    (len ≡ lengthZ s)

size-alt'vc : Set₁
size-alt'vc =
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
  ∧ ((len : Int) →
     (p : Loc sig) →
     dll
       sig
       (toFMap sig prev)
       (toFMap sig next)
       s
       p
       len
       (lengthZ s)
     →
     loopObligation
       sig
       (toFMap sig prev)
       (toFMap sig next)
       s
       len
       p)
