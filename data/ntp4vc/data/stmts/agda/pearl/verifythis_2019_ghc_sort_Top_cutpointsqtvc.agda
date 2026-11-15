-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2019_ghc_sort_Top_cutpointsqtvc: the verification
-- condition for constructing ordered cutpoints that partition a nonempty
-- integer sequence into monotonic segments. This file contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2019GhcSortTopCutpointsVC where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_ _∈_
infixr 3 _∧_
infixr 2 _∨_
infix 1 _↔_

record Top : Set where
  constructor top

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

data _∈_ {A : Set} (x : A) : List A → Set where
  here  : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

boolImplies : Bool → Bool → Bool
boolImplies false _ = true
boolImplies true b = b

boolAnd : Bool → Bool → Bool
boolAnd true b = b
boolAnd false _ = false

eqb : Bool → Bool → Bool
eqb b₁ b₂ =
  boolAnd (boolImplies b₁ b₂) (boolImplies b₂ b₁)

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

natToInt : Nat → Int
natToInt = pos

zeroZ oneZ twoZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = natToInt (length xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) = nthDefault default n xs

nthInt : List Int → Int → Int
nthInt xs index = nthDefault zeroZ (toNat index) xs

append : {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = append (reverse xs) (x ∷ [])

record ListSeq : Set where
  constructor listSeq
  field
    list      : List Int
    seq       : List Int
    invariant : seq ≡ reverse list

open ListSeq

nil : ListSeq
nil = listSeq [] [] refl

lastCut : ListSeq → Int
lastCut cut =
  nthInt (seq cut) (subtractInt (lengthZ (seq cut)) oneZ)

WithinBounds : List Int → Int → Set
WithinBounds values upper =
  (z : Int) →
  z ∈ values →
  (zeroZ ≤Z z) ∧ (z ≤Z upper)

IncreasingSegment : List Int → Int → Int → Set
IncreasingSegment values lower upper =
  (z₁ z₂ : Int) →
  ((lower ≤Z z₁) ∧ (z₁ <Z z₂) ∧ (z₂ <Z upper)) →
  nthInt values z₁ <Z nthInt values z₂

DecreasingSegment : List Int → Int → Int → Set
DecreasingSegment values lower upper =
  (z₁ z₂ : Int) →
  ((lower ≤Z z₁) ∧ (z₁ <Z z₂) ∧ (z₂ <Z upper)) →
  nthInt values z₂ ≤Z nthInt values z₁

MonotonicSegment : List Int → Int → Int → Set
MonotonicSegment values lower upper =
  IncreasingSegment values lower upper ∨
  DecreasingSegment values lower upper

AllSegmentsMonotonic : List Int → ListSeq → Set
AllSegmentsMonotonic values cut =
  (k : Int) →
  ((zeroZ ≤Z k) ∧
   (k <Z subtractInt (lengthZ (seq cut)) oneZ)) →
  let ck = nthInt (seq cut) k
      ck₁ = nthInt (seq cut) (addInt k oneZ)
  in
  MonotonicSegment values ck ck₁

OrderedCutpoints : ListSeq → Set
OrderedCutpoints cut =
  (i j : Int) →
  ((zeroZ ≤Z i) ∧ (i <Z j) ∧
   (j <Z lengthZ (seq cut))) →
  nthInt (seq cut) i ≤Z nthInt (seq cut) j

CutInvariant : List Int → Int → ListSeq → Set
CutInvariant values n cut =
  ((zeroZ <Z addInt (lastCut cut) oneZ) ∧
   (addInt (lastCut cut) oneZ ≤Z addInt n oneZ)) ∧
  (zeroZ <Z lengthZ (seq cut)) ∧
  (nthInt (seq cut) zeroZ ≡ zeroZ) ∧
  WithinBounds (list cut) n ∧
  AllSegmentsMonotonic values cut ∧
  OrderedCutpoints cut

InitialCutInvariant : List Int → Int → ListSeq → Set
InitialCutInvariant values n initial =
  (oneZ ≡ addInt zeroZ oneZ) ∧
  ((zeroZ <Z oneZ) ∧
   (oneZ ≤Z addInt n oneZ)) ∧
  (zeroZ <Z lengthZ (seq initial)) ∧
  (nthInt (seq initial) zeroZ ≡ zeroZ) ∧
  (lastCut initial ≡ zeroZ) ∧
  WithinBounds (list initial) n ∧
  AllSegmentsMonotonic values initial ∧
  OrderedCutpoints initial

IndexInBounds : List Int → Int → Set
IndexInBounds values index =
  (zeroZ ≤Z index) ∧ (index <Z lengthZ values)

ExtendedCutInvariant :
  List Int →
  Int →
  ListSeq →
  Int →
  Int →
  Set
ExtendedCutInvariant values n extended previous next =
  ((zeroZ ≤Z subtractInt n (addInt previous oneZ)) ∧
   (subtractInt n (addInt next oneZ) <Z
    subtractInt n (addInt previous oneZ))) ∧
  ((zeroZ <Z addInt next oneZ) ∧
   (addInt next oneZ ≤Z addInt n oneZ)) ∧
  (zeroZ <Z lengthZ (seq extended)) ∧
  (nthInt (seq extended) zeroZ ≡ zeroZ) ∧
  (lastCut extended ≡ next) ∧
  WithinBounds (list extended) n ∧
  AllSegmentsMonotonic values extended ∧
  OrderedCutpoints extended

ContinueSameSegment :
  List Int →
  Int →
  ListSeq →
  Int →
  Set
ContinueSameSegment values n cut y =
  ((zeroZ ≤Z subtractInt n y) ∧
   (subtractInt n (addInt y oneZ) <Z
    subtractInt n y)) ∧
  ((addInt (lastCut cut) oneZ ≤Z addInt y oneZ) ∧
   (addInt y oneZ ≤Z n)) ∧
  MonotonicSegment values (lastCut cut) (addInt y oneZ)

CurrentDirection : List Int → Int → Bool
CurrentDirection values y =
  intLess
    (nthInt values (subtractInt y oneZ))
    (nthInt values y)

BaseDirection : List Int → ListSeq → Bool
BaseDirection values cut =
  intLess
    (nthInt values (lastCut cut))
    (nthInt values (addInt (lastCut cut) oneZ))

DirectionAgreement :
  List Int →
  Int →
  ListSeq →
  Int →
  Bool →
  Set
DirectionAgreement values n cut y same-direction =
  IfSet (intLess y n)
    ((same-direction ≡
      eqb
        (CurrentDirection values y)
        (BaseDirection values cut)) ∧
     ((same-direction ≡ true) ↔
      (CurrentDirection values y ≡
       BaseDirection values cut)))
    (same-direction ≡ false)

InnerLoopConclusion :
  List Int →
  Int →
  ListSeq →
  Int →
  Bool →
  Set
InnerLoopConclusion values n cut y same-direction =
  IfSet same-direction
    (ContinueSameSegment values n cut y)
    ((extended : ListSeq) →
     list extended ≡ y ∷ list cut →
     ExtendedCutInvariant
       values n extended (lastCut cut) y)

InnerLoopVC : List Int → Int → ListSeq → Int → Set
InnerLoopVC values n cut y =
  (((addInt (lastCut cut) oneZ ≤Z y) ∧
    (y ≤Z n)) ∧
   MonotonicSegment values (lastCut cut) y) →
  ((y <Z n) →
   (IndexInBounds values y ∧
    IndexInBounds values (subtractInt y oneZ))) ∧
  ((same-direction : Bool) →
   DirectionAgreement values n cut y same-direction →
   InnerLoopConclusion values n cut y same-direction)

ScanningBranch : List Int → Int → ListSeq → Set
ScanningBranch values n cut =
  IndexInBounds values (addInt (lastCut cut) oneZ) ∧
  IndexInBounds values (lastCut cut) ∧
  (((addInt (lastCut cut) oneZ ≤Z
     addInt (lastCut cut) oneZ) ∧
    (addInt (lastCut cut) oneZ ≤Z n)) ∧
   MonotonicSegment
     values
     (lastCut cut)
     (addInt (lastCut cut) oneZ)) ∧
  ((y : Int) → InnerLoopVC values n cut y)

FinalCut : List Int → ListSeq → Set
FinalCut values cut =
  (nthInt (seq cut) zeroZ ≡ zeroZ) ∧
  (lastCut cut ≡ lengthZ values) ∧
  (twoZ ≤Z lengthZ (list cut)) ∧
  WithinBounds (list cut) (lengthZ values) ∧
  AllSegmentsMonotonic values cut ∧
  OrderedCutpoints cut

AppendFinalCut : List Int → Int → ListSeq → Set
AppendFinalCut values n cut =
  (extended : ListSeq) →
  list extended ≡ n ∷ list cut →
  FinalCut values extended

CutBody : List Int → Int → ListSeq → Set
CutBody values n cut =
  IfSet (intLess (addInt (lastCut cut) oneZ) n)
    (ScanningBranch values n cut)
    (IfSet (intLess (lastCut cut) n)
      (AppendFinalCut values n cut)
      (FinalCut values cut))

cutpoints'vc : Set
cutpoints'vc =
  (values : List Int) →
  zeroZ <Z lengthZ values →
  let n = lengthZ values
  in
  (initial : ListSeq) →
  list initial ≡ zeroZ ∷ list nil →
  InitialCutInvariant values n initial ∧
  ((cut : ListSeq) →
   CutInvariant values n cut →
   CutBody values n cut)
