-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/mergesort_array_NaturalMergesort_natural_mergesortqtvc: the natural
-- mergesort verification condition, preserving sorted runs and permutation
-- through run discovery and merge-loop transitions. This file contains no
-- proof.

{-# OPTIONS --safe #-}

module mergesort_array_NaturalMergesort_natural_mergesortqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

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

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

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

module NaturalMergesortTheory
  (Elt : Set)
  (eltDefault : Elt)
  (le : Elt → Elt → Set)
  (leRefl : (x : Elt) → le x x)
  (leTrans :
    (x y z : Elt) → le x y → le y z → le x z)
  (leTotal : (x y : Elt) → le x y ∨ le y x)
  where

  nthElt : List Elt → Int → Elt
  nthElt xs index = nthDefault eltDefault (toNat index) xs

  sortedSub : List Elt → Int → Int → Set
  sortedSub xs lower upper =
    (i₁ i₂ : Int) →
    ((lower ≤Z i₁) ∧ (i₁ <Z i₂) ∧ (i₂ <Z upper)) →
    le (nthElt xs i₁) (nthElt xs i₂)

  sorted : List Elt → Set
  sorted xs = sortedSub xs zeroZ (lengthZ xs)

  OutsideEqual :
    List Elt →
    List Elt →
    Int →
    Int →
    Set
  OutsideEqual before after lower upper =
    (i : Int) →
    (((zeroZ ≤Z i) ∧ (i <Z lower)) ∨
     ((upper ≤Z i) ∧ (i <Z lengthZ after))) →
    nthElt after i ≡ nthElt before i

  TemporaryCopy :
    List Elt →
    List Elt →
    Set
  TemporaryCopy original temporary =
    (length temporary ≡ length original) ∧
    ((i : Int) →
      ((zeroZ ≤Z i) ∧ (i <Z lengthZ temporary)) →
      nthElt temporary i ≡ nthElt original i)

  InitialState :
    List Elt →
    Int →
    Set
  InitialState original n =
    (((zeroZ ≤Z zeroZ) ∧ (zeroZ ≤Z n)) ∧
     sortedSub original zeroZ zeroZ) ∧
    Perm original original

  FirstRunPremise :
    List Elt →
    List Elt →
    Int →
    Int →
    Set
  FirstRunPremise original current n first-run =
    (((zeroZ ≤Z first-run) ∧ (first-run ≤Z n)) ∧
     sortedSub current zeroZ first-run) ∧
    Perm original current

  FirstRunState :
    List Elt →
    Int →
    Int →
    Set
  FirstRunState current n first-run =
    ((zeroZ ≤Z zeroZ) ∧ (zeroZ ≤Z n)) ∧
    (first-run ≤Z first-run) ∧
    (first-run ≤Z n) ∧
    sortedSub current zeroZ first-run ∧
    Perm current current

  ScanPremise :
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Int →
    Set
  ScanPremise before current n first-run lo first-run₁ =
    ((zeroZ ≤Z lo) ∧ (lo ≤Z n)) ∧
    ((first-run ≤Z first-run₁) ∧ (first-run₁ ≤Z n)) ∧
    sortedSub current zeroZ first-run₁ ∧
    ((lo ≡ zeroZ) ∨
     ((first-run₁ ≤Z lo) ∧ (first-run <Z first-run₁))) ∧
    Perm before current

  DecreasingFirstRun :
    Int →
    Int →
    Int →
    Set
  DecreasingFirstRun n first-run first-run₁ =
    (zeroZ ≤Z subtractInt n first-run) ∧
    (subtractInt n first-run₁ <Z subtractInt n first-run)

  FirstRunInvariant :
    List Elt →
    Int →
    Int →
    Set
  FirstRunInvariant current n first-run₁ =
    (((zeroZ ≤Z first-run₁) ∧ (first-run₁ ≤Z n)) ∧
     sortedSub current zeroZ first-run₁)

  ContinueWithFirstRun :
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Set
  ContinueWithFirstRun original current n first-run first-run₁ =
    DecreasingFirstRun n first-run first-run₁ ∧
    FirstRunInvariant current n first-run₁ ∧
    Perm original current

  MergeSetup :
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Set
  MergeSetup temporary current lo mid hi =
    ((zeroZ ≤Z lo) ∧
     (lo ≤Z mid) ∧
     (mid ≤Z hi) ∧
     (hi ≤Z lengthZ temporary) ∧
     (length temporary ≡ length current)) ∧
    sortedSub current lo mid ∧
    sortedSub current mid hi

  MergeResultPremise :
    List Elt →
    List Elt →
    Int →
    Int →
    Set
  MergeResultPremise before after lo hi =
    sortedSub after lo hi ∧
    permutSub before after (toNat lo) (toNat hi) ∧
    OutsideEqual before after lo hi

  MergeAtZeroConclusion :
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Int →
    Set
  MergeAtZeroConclusion before result n first-run hi lo =
    ((zeroZ ≤Z subtractInt n lo) ∧
     (subtractInt n hi <Z subtractInt n lo)) ∧
    ((zeroZ ≤Z hi) ∧ (hi ≤Z n)) ∧
    ((first-run ≤Z hi) ∧ (hi ≤Z n)) ∧
    sortedSub result zeroZ hi ∧
    ((hi ≡ zeroZ) ∨
     ((hi ≤Z hi) ∧ (first-run <Z hi))) ∧
    Perm before result

  MergeAfterZeroConclusion :
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Int →
    Int →
    Set
  MergeAfterZeroConclusion
    before result n first-run first-run₁ hi lo =
    ((zeroZ ≤Z subtractInt n lo) ∧
     (subtractInt n hi <Z subtractInt n lo)) ∧
    ((zeroZ ≤Z hi) ∧ (hi ≤Z n)) ∧
    ((first-run ≤Z first-run₁) ∧ (first-run₁ ≤Z n)) ∧
    sortedSub result zeroZ first-run₁ ∧
    ((hi ≡ zeroZ) ∨
     ((first-run₁ ≤Z hi) ∧ (first-run <Z first-run₁))) ∧
    Perm before result

  MergeResultConclusion :
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Int →
    Int →
    Set
  MergeResultConclusion
    before result n first-run first-run₁ lo hi =
    IfSet
      (intEqual lo zeroZ)
      (MergeAtZeroConclusion
        before result n first-run hi lo)
      (MergeAfterZeroConclusion
        before result n first-run first-run₁ hi lo)

  AfterMerge :
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Int →
    Int →
    Set
  AfterMerge before current n first-run first-run₁ lo hi =
    (result : List Elt) →
    (length result ≡ length current) →
    MergeResultPremise current result lo hi →
    MergeResultConclusion
      before result n first-run first-run₁ lo hi

  ScanLoop :
    List Elt →
    List Elt →
    List Elt →
    Int →
    Int →
    Set
  ScanLoop original before temporary n first-run =
    (lo first-run₁ : Int) →
    (temporary₂ current : List Elt) →
    (length temporary₂ ≡ length temporary) →
    (length current ≡ length before) →
    ScanPremise before current n first-run lo first-run₁ →
    IfSet
      (intLess lo (subtractInt n oneZ))
      ((zeroZ ≤Z lo) ∧
       (lo <Z lengthZ current) ∧
       ((mid : Int) →
        (((lo <Z mid) ∧ (mid ≤Z lengthZ current)) ∧
         sortedSub current lo mid ∧
         ((mid <Z lengthZ current) →
          Not
            (le
              (nthElt current (subtractInt mid oneZ))
              (nthElt current mid)))) →
        IfSet
          (intEqual mid n)
          (IfSet
            (intEqual lo zeroZ)
            (sorted current ∧ Perm original current)
            (ContinueWithFirstRun
              original current n first-run first-run₁))
          ((zeroZ ≤Z mid) ∧
           (mid <Z lengthZ current) ∧
           ((hi : Int) →
            (((mid <Z hi) ∧ (hi ≤Z lengthZ current)) ∧
             sortedSub current mid hi ∧
             ((hi <Z lengthZ current) →
              Not
                (le
                  (nthElt current (subtractInt hi oneZ))
                  (nthElt current hi)))) →
            (MergeSetup temporary₂ current lo mid hi ∧
             ((result : List Elt) →
              (length result ≡ length current) →
              MergeResultPremise current result lo hi →
              MergeResultConclusion
                before
                result
                n
                first-run
                first-run₁
                lo
                hi))))))
      (ContinueWithFirstRun
        original current n first-run first-run₁)

  FirstRunLoop :
    List Elt →
    List Elt →
    Int →
    Set
  FirstRunLoop original temporary n =
    (first-run : Int) →
    (temporary₁ current : List Elt) →
    (length temporary₁ ≡ length temporary) →
    (length current ≡ length original) →
    FirstRunPremise original current n first-run →
    FirstRunState current n first-run ∧
    ScanLoop original current temporary₁ n first-run

  NontrivialCase :
    List Elt →
    Int →
    Set
  NontrivialCase original n =
    (temporary : List Elt) →
    TemporaryCopy original temporary →
    InitialState original n ∧
    FirstRunLoop original temporary n

  NaturalMergesortVC : List Elt → Set
  NaturalMergesortVC original =
    let n = lengthZ original
    in
    IfSet
      (intLessOrEqual n oneZ)
      (sorted original ∧ Perm original original)
      (NontrivialCase original n)

  natural-mergesort'vc : Set
  natural-mergesort'vc =
    (original : List Elt) →
    NaturalMergesortVC original
