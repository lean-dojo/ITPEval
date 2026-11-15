-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/mergesort_array_NaturalMergesort_naturalrecqtvc: the natural
-- mergesort recursive verification condition for sorted runs, subarray
-- permutations, and nested loop continuations. This file contains no proof.

{-# OPTIONS --safe #-}

module mergesort_array_NaturalMergesort_naturalrecqtvc where

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

permutSubPrime : {A : Set} → List A → List A → Nat → Nat → Set
permutSubPrime xs ys lower upper =
  (length xs ≡ length ys) ∧
  (slice xs zero lower ≡ slice ys zero lower) ∧
  (slice xs upper (length xs) ≡ slice ys upper (length xs)) ∧
  Perm (slice xs lower upper) (slice ys lower upper)

module NaturalRecTheory
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

  prefixUnchanged :
    List Elt →
    List Elt →
    Int →
    Set
  prefixUnchanged current original upper =
    (index : Int) →
    ((zeroZ ≤Z index) ∧ (index <Z upper)) →
    nthElt current index ≡ nthElt original index

  unchangedOutside :
    List Elt →
    List Elt →
    Int →
    Int →
    Set
  unchangedOutside current previous lower upper =
    (index : Int) →
    (((zeroZ ≤Z index) ∧ (index <Z lower)) ∨
     ((upper ≤Z index) ∧ (index <Z lengthZ current))) →
    nthElt current index ≡ nthElt previous index

  SelfResult :
    List Elt →
    Int →
    Int →
    Int →
    Set
  SelfResult a lo k endpoint =
    ((endpoint ≡ lengthZ a) ∨
     ((addInt lo k <Z endpoint) ∧ (endpoint <Z lengthZ a))) ∧
    sortedSub a lo endpoint ∧
    permutSubPrime a a (toNat lo) (length a)

  ProgressResult :
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Set
  ProgressResult original current lo k endpoint =
    ((endpoint ≡ lengthZ current) ∨
     ((addInt lo k <Z endpoint) ∧
      (endpoint <Z lengthZ current))) ∧
    sortedSub current lo endpoint ∧
    permutSubPrime original current (toNat lo) (length current) ∧
    prefixUnchanged current original lo

  AfterA3 :
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Int →
    Int →
    Set
  AfterA3 original a₃ lo k i hi n =
    IfSet
      (intEqual hi n)
      (ProgressResult original a₃ lo k n)
      (((addInt lo (addInt i oneZ) <Z hi) ∧ (hi <Z n)) ∧
       sortedSub a₃ lo hi ∧
       permutSubPrime original a₃ (toNat lo) (length a₃) ∧
       prefixUnchanged a₃ original lo)

  AllA3 :
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Int →
    Int →
    Set
  AllA3 original a₂ lo k i hi n =
    (a₃ : List Elt) →
    (length a₃ ≡ length a₂) →
    (sortedSub a₃ lo hi ∧
     permutSub a₂ a₃ (toNat lo) (toNat hi) ∧
     unchangedOutside a₃ a₂ lo hi) →
    AfterA3 original a₃ lo k i hi n

  HiConclusion :
    List Elt →
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Int →
    Int →
    Int →
    Set
  HiConclusion original a₂ tmp₂ lo k i mid hi n =
    (((zeroZ ≤Z lo) ∧
      (lo ≤Z mid) ∧
      (mid ≤Z hi) ∧
      (hi ≤Z lengthZ tmp₂) ∧
      (length tmp₂ ≡ length a₂)) ∧
     sortedSub a₂ lo mid ∧
     sortedSub a₂ mid hi) ∧
    AllA3 original a₂ lo k i hi n

  AllHi :
    List Elt →
    List Elt →
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Int →
    Int →
    Set
  AllHi original a₁ a₂ tmp₂ lo k i mid n =
    (hi : Int) →
    (((hi ≡ lengthZ a₂) ∨
      ((addInt mid i <Z hi) ∧ (hi <Z lengthZ a₂))) ∧
     sortedSub a₂ mid hi ∧
     permutSubPrime a₁ a₂ (toNat mid) (length a₂) ∧
     prefixUnchanged a₂ a₁ mid) →
    HiConclusion original a₂ tmp₂ lo k i mid hi n

  AllA2Tmp2 :
    List Elt →
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Int →
    Int →
    Set
  AllA2Tmp2 original a₁ tmp₁ lo k i mid n =
    (a₂ tmp₂ : List Elt) →
    (length a₂ ≡ length a₁) →
    (length tmp₂ ≡ length tmp₁) →
    AllHi original a₁ a₂ tmp₂ lo k i mid n

  IConclusion :
    List Elt →
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Int →
    Int →
    Set
  IConclusion original a₁ tmp₁ lo k i mid n =
    ((zeroZ ≤Z k) ∧ (i <Z k)) ∧
    ((zeroZ ≤Z mid) ∧
     (mid ≤Z lengthZ a₁) ∧
     (length a₁ ≡ length tmp₁)) ∧
    (zeroZ ≤Z i) ∧
    AllA2Tmp2 original a₁ tmp₁ lo k i mid n

  AllI :
    List Elt →
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Int →
    Int →
    Set
  AllI original a₁ tmp₁ lo k o₂ mid n =
    (i : Int) →
    (((zeroZ ≤Z i) ∧ (i ≤Z o₂)) ∧
     ((addInt lo i <Z mid) ∧ (mid <Z n)) ∧
     sortedSub a₁ lo mid ∧
     permutSubPrime original a₁ (toNat lo) (length a₁) ∧
     prefixUnchanged a₁ original lo) →
    IConclusion original a₁ tmp₁ lo k i mid n

  MidClosure :
    List Elt →
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Int →
    Int →
    Set
  MidClosure original a₁ tmp₁ lo k o₂ mid n =
    AllI original a₁ tmp₁ lo k o₂ mid n ∧
    ((((addInt lo (addInt o₂ oneZ) <Z mid) ∧ (mid <Z n)) ∧
      sortedSub a₁ lo mid ∧
      permutSubPrime original a₁ (toNat lo) (length a₁) ∧
      prefixUnchanged a₁ original lo) →
     ProgressResult original a₁ lo k mid)

  AllMid :
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Int →
    Set
  AllMid original tmp lo k o₂ n =
    (mid : Int) →
    (a₁ tmp₁ : List Elt) →
    (length a₁ ≡ length original) →
    (length tmp₁ ≡ length tmp) →
    MidClosure original a₁ tmp₁ lo k o₂ mid n

  O2NonnegativeResult :
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Int →
    Int →
    Set
  O2NonnegativeResult a tmp lo k o₁ o₂ n =
    (((addInt lo zeroZ <Z o₁) ∧ (o₁ <Z n)) ∧
     sortedSub a lo o₁ ∧
     permutSubPrime a a (toNat lo) (length a)) ∧
    AllMid a tmp lo k o₂ n

  O1NonfinalCase :
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Int →
    Set
  O1NonfinalCase a tmp lo k o₁ n =
    let o₂ = subtractInt k oneZ
    in
    ((zeroZ ≤Z addInt o₂ oneZ) →
     O2NonnegativeResult a tmp lo k o₁ o₂ n) ∧
    ((addInt o₂ oneZ <Z zeroZ) →
     SelfResult a lo k o₁)

  O1Case :
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Int →
    Set
  O1Case a tmp lo k o₁ n =
    IfSet
      (intEqual o₁ n)
      (SelfResult a lo k n)
      (O1NonfinalCase a tmp lo k o₁ n)

  AllO1 :
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Set
  AllO1 a tmp lo k n =
    (o₁ : Int) →
    (((lo <Z o₁) ∧ (o₁ ≤Z lengthZ a)) ∧
     sortedSub a lo o₁ ∧
     ((o₁ <Z lengthZ a) →
      Not
        (le
          (nthElt a (subtractInt o₁ oneZ))
          (nthElt a o₁)))) →
    O1Case a tmp lo k o₁ n

  RecursiveBranch :
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Set
  RecursiveBranch a tmp lo k n =
    ((zeroZ ≤Z lo) ∧ (lo <Z lengthZ a)) ∧
    AllO1 a tmp lo k n

  NaturalRecVC :
    Int →
    List Elt →
    List Elt →
    Int →
    Set
  NaturalRecVC lo a tmp k =
    (zeroZ ≤Z lo) →
    (lo ≤Z lengthZ a) →
    (length a ≡ length tmp) →
    (zeroZ ≤Z k) →
    let n = lengthZ a
    in
    IfSet
      (intLessOrEqual (subtractInt n oneZ) lo)
      (SelfResult a lo k n)
      (RecursiveBranch a tmp lo k n)

  naturalrec'vc : Set
  naturalrec'vc =
    (lo : Int) →
    (a tmp : List Elt) →
    (k : Int) →
    NaturalRecVC lo a tmp k
