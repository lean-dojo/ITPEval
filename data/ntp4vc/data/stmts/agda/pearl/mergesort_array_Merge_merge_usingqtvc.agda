-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/mergesort_array_Merge_merge_usingqtvc: the merge verification
-- condition for adjacent sorted array subranges, preserving subrange
-- permutation and values outside the merged interval. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module mergesort_array_Merge_merge_usingqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≤N_ _≤Z_ _<Z_
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
  left  : A → A ∨ B
  right : B → A ∨ B

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : Not P → Dec P

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

IfDec : {P : Set} → Dec P → Set → Set → Set
IfDec (yes _) when-true when-false = when-true
IfDec (no _) when-true when-false = when-false

IfBool : Bool → Bool → Bool → Bool
IfBool true when-true when-false = when-true
IfBool false when-true when-false = when-false

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

_≤N_ : Nat → Nat → Set
x ≤N y = natLessOrEqual x y ≡ true

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
addInt (pos m) (pos n) = pos (m Agda.Builtin.Nat.+ n)
addInt (pos m) (negsuc n) = differenceNat m (suc n)
addInt (negsuc m) (pos n) = differenceNat n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m Agda.Builtin.Nat.+ n))

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

natToInt : Nat → Int
natToInt = pos

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = natToInt (length xs)

natSubtract : Nat → Nat → Nat
natSubtract n zero = n
natSubtract zero (suc _) = zero
natSubtract (suc m) (suc n) = natSubtract m n

take : {A : Set} → Nat → List A → List A
take zero _ = []
take (suc _) [] = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : {A : Set} → Nat → List A → List A
drop zero xs = xs
drop (suc _) [] = []
drop (suc n) (_ ∷ xs) = drop n xs

slice : {A : Set} → List A → Nat → Nat → List A
slice xs lower upper =
  take (natSubtract upper lower) (drop lower xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) = nthDefault default n xs

data Perm {A : Set} : List A → List A → Set where
  permNil :
    Perm [] []

  permKeep :
    {x : A} {xs ys : List A} →
    Perm xs ys →
    Perm (x ∷ xs) (x ∷ ys)

  permSwap :
    (x y : A) →
    (xs : List A) →
    Perm (x ∷ y ∷ xs) (y ∷ x ∷ xs)

  permTrans :
    {xs ys zs : List A} →
    Perm xs ys →
    Perm ys zs →
    Perm xs zs

permutSub : {A : Set} → List A → List A → Nat → Nat → Set
permutSub xs ys lower upper =
  (length xs ≡ length ys) ∧
  ((zero ≤N lower) ∧ (lower ≤N length xs)) ∧
  ((zero ≤N upper) ∧ (upper ≤N length xs)) ∧
  Perm (slice xs lower upper) (slice ys lower upper)

module MergeTheory
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

  nthElt : List Elt → Int → Elt
  nthElt xs index = nthDefault eltDefault (toNat index) xs

  sortedSub : List Elt → Int → Int → Set
  sortedSub xs lower upper =
    (i₁ i₂ : Int) →
    ((lower ≤Z i₁) ∧ (i₁ <Z i₂) ∧ (i₂ <Z upper)) →
    le (nthElt xs i₁) (nthElt xs i₂)

  sorted : List Elt → Set
  sorted xs = sortedSub xs zeroZ (lengthZ xs)

  OutsideTemporary :
    List Elt →
    List Elt →
    Int →
    Int →
    Set
  OutsideTemporary before after lower copiedLength =
    (i : Int) →
    (((zeroZ ≤Z i) ∧ (i <Z lower)) ∨
     ((addInt lower copiedLength ≤Z i) ∧
      (i <Z lengthZ after))) →
    nthElt after i ≡ nthElt before i

  InsideTemporary :
    List Elt →
    List Elt →
    Int →
    Int →
    Set
  InsideTemporary source destination lower copiedLength =
    (i : Int) →
    ((lower ≤Z i) ∧ (i <Z addInt lower copiedLength)) →
    nthElt destination i ≡
      nthElt source (subtractInt (addInt lower i) lower)

  ReadyForMerge :
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Set
  ReadyForMerge temporary current lower middle upper =
    ((zeroZ ≤Z lower) ∧
     (lower ≤Z middle) ∧
     (middle ≤Z upper) ∧
     (upper ≤Z lengthZ temporary) ∧
     (length temporary ≡ length current)) ∧
    sortedSub temporary lower middle ∧
    sortedSub temporary middle upper

  OutsideOriginal :
    List Elt →
    List Elt →
    Int →
    Int →
    Set
  OutsideOriginal original result lower upper =
    (i : Int) →
    (((zeroZ ≤Z i) ∧ (i <Z lower)) ∨
     ((upper ≤Z i) ∧ (i <Z lengthZ result))) →
    nthElt result i ≡ nthElt original i

  MergeResultPremise :
    List Elt →
    List Elt →
    List Elt →
    Int →
    Int →
    Set
  MergeResultPremise temporary original result lower upper =
    sortedSub result lower upper ∧
    permutSub temporary result (toNat lower) (toNat upper) ∧
    OutsideOriginal original result lower upper

  MergeResultConclusion :
    List Elt →
    List Elt →
    Int →
    Int →
    Set
  MergeResultConclusion original result lower upper =
    sortedSub result lower upper ∧
    permutSub original result (toNat lower) (toNat upper) ∧
    OutsideOriginal original result lower upper

  AfterCopy :
    List Elt →
    List Elt →
    Int →
    Int →
    Set
  AfterCopy temporary original lower upper =
    (result : List Elt) →
    (length result ≡ length original) →
    MergeResultPremise temporary original result lower upper →
    MergeResultConclusion original result lower upper

  CopiedTemporaryObligation :
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Set
  CopiedTemporaryObligation original temporary lower middle upper =
    let copiedLength = subtractInt upper lower
    in
    (temporary₁ : List Elt) →
    (length temporary₁ ≡ length temporary) →
    (OutsideTemporary temporary temporary₁ lower copiedLength ∧
     InsideTemporary original temporary₁ lower copiedLength) →
    ReadyForMerge temporary₁ original lower middle upper ∧
    AfterCopy temporary₁ original lower upper

  CopyBranch :
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Set
  CopyBranch original temporary lower middle upper =
    let copiedLength = subtractInt upper lower
        copiedEnd = addInt lower copiedLength
    in
    (((zeroZ ≤Z lower) ∧
      (zeroZ ≤Z copiedLength) ∧
      (copiedEnd ≤Z lengthZ original)) ∧
     (zeroZ ≤Z lower) ∧
     (copiedEnd ≤Z lengthZ temporary)) ∧
    CopiedTemporaryObligation
      original temporary lower middle upper

  TrueBranch :
    Int →
    Int →
    Int →
    List Elt →
    List Elt →
    Set
  TrueBranch lower middle upper temporary original =
    ((zeroZ ≤Z middle) ∧ (middle <Z lengthZ original)) ∧
    (let previous = subtractInt middle oneZ
     in
     ((zeroZ ≤Z previous) ∧
      (previous <Z lengthZ original)) ∧
     IfDec
       (decide (le (nthElt original previous)
                   (nthElt original middle)))
       (sortedSub original lower upper ∧
        permutSub original original (toNat lower) (toNat upper))
       (CopyBranch original temporary lower middle upper))

  MergeUsingVC :
    Int →
    Int →
    Int →
    List Elt →
    List Elt →
    Bool →
    Set
  MergeUsingVC lower middle upper temporary original branch =
    (zeroZ ≤Z lower) →
    (lower ≤Z middle) →
    (middle ≤Z upper) →
    (upper ≤Z lengthZ temporary) →
    (length temporary ≡ length original) →
    sortedSub original lower middle →
    sortedSub original middle upper →
    (branch ≡
      IfBool
        (intLess lower middle)
        (IfBool (intLess middle upper) true false)
        false) →
    IfSet
      branch
      (TrueBranch lower middle upper temporary original)
      (sortedSub original lower upper ∧
       permutSub original original (toNat lower) (toNat upper))

  merge-using'vc : Set
  merge-using'vc =
    (lower middle upper : Int) →
    (temporary original : List Elt) →
    (branch : Bool) →
    MergeUsingVC lower middle upper temporary original branch
