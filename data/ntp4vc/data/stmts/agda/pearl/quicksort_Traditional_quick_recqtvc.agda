-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/quicksort_Traditional_quick_recqtvc: the traditional quicksort
-- recursive verification condition, including bidirectional partition scans,
-- swaps, recursive sorted subranges, and subarray permutations. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module quicksort_Traditional_quick_recqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

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

nthInt : List Int → Int → Int
nthInt xs index = nthDefault zeroZ (toNat index) xs

setAt : {A : Set} → List A → Nat → A → List A
setAt [] _ value = []
setAt (_ ∷ xs) zero value = value ∷ xs
setAt (x ∷ xs) (suc n) value = x ∷ setAt xs n value

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

permutSub' : {A : Set} → List A → List A → Nat → Nat → Set
permutSub' xs ys lower upper =
  (length xs ≡ length ys) ∧
  (slice xs zero lower ≡ slice ys zero lower) ∧
  (slice xs upper (length xs) ≡ slice ys upper (length xs)) ∧
  Perm (slice xs lower upper) (slice ys lower upper)

arrayExchange : List Int → List Int → Int → Int → Set
arrayExchange old new first-index second-index =
  new ≡
    setAt
      (setAt old
        (toNat first-index)
        (nthInt old second-index))
      (toNat second-index)
      (nthInt old first-index)

sortedSub1 : List Int → Int → Int → Set
sortedSub1 xs lower upper =
  (i₁ i₂ : Int) →
  ((lower ≤Z i₁) ∧ (i₁ ≤Z i₂) ∧ (i₂ <Z upper)) →
  nthInt xs i₁ ≤Z nthInt xs i₂

AllLeClosed : List Int → Int → Int → Int → Set
AllLeClosed xs lower upper pivot =
  (index : Int) →
  ((lower ≤Z index) ∧ (index ≤Z upper)) →
  nthInt xs index ≤Z pivot

AllLeHalfOpen : List Int → Int → Int → Int → Set
AllLeHalfOpen xs lower upper pivot =
  (index : Int) →
  ((lower ≤Z index) ∧ (index <Z upper)) →
  nthInt xs index ≤Z pivot

AllGeHalfOpen : List Int → Int → Int → Int → Set
AllGeHalfOpen xs lower upper pivot =
  (index : Int) →
  ((lower ≤Z index) ∧ (index <Z upper)) →
  pivot ≤Z nthInt xs index

AllGeOpen : List Int → Int → Int → Int → Set
AllGeOpen xs lower upper pivot =
  (index : Int) →
  ((lower <Z index) ∧ (index <Z upper)) →
  pivot ≤Z nthInt xs index

LoopInvariant :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Set
LoopInvariant original current lower upper j i pivot =
  ((lower ≤Z i) ∧ (i <Z subtractInt upper oneZ)) ∧
  AllLeClosed current lower i pivot ∧
  ((lower <Z j) ∧ (j ≤Z upper)) ∧
  AllGeHalfOpen current j upper pivot ∧
  permutSub' original current (toNat lower) (toNat upper) ∧
  nthInt current lower ≡ pivot

AfterRightRecursion :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Set
AfterRightRecursion original after-left lower right-lower upper =
  (after-right : List Int) →
  length after-right ≡ length after-left →
  (sortedSub1 after-right right-lower upper ∧
   permutSub'
     after-left
     after-right
     (toNat right-lower)
     (toNat upper)) →
  sortedSub1 after-right lower upper ∧
  permutSub'
    original
    after-right
    (toNat lower)
    (toNat upper)

AfterLeftRecursion :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Set
AfterLeftRecursion original after-swap lower middle upper =
  (after-left : List Int) →
  length after-left ≡ length after-swap →
  (sortedSub1 after-left lower middle ∧
   permutSub'
     after-swap
     after-left
     (toNat lower)
     (toNat middle)) →
  let right-lower = addInt middle oneZ
  in
  (((zeroZ ≤Z subtractInt upper lower) ∧
    (subtractInt upper right-lower
      <Z subtractInt upper lower)) ∧
   ((zeroZ ≤Z right-lower) ∧
    (right-lower ≤Z upper) ∧
    (upper ≤Z lengthZ after-left))) ∧
  AfterRightRecursion
    original
    after-left
    lower
    right-lower
    upper

FinishSwapContinuation :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Set
FinishSwapContinuation original current lower upper j₁ =
  (after-swap : List Int) →
  length after-swap ≡ length current →
  arrayExchange current after-swap lower j₁ →
  ((((zeroZ ≤Z subtractInt upper lower) ∧
     (subtractInt j₁ lower <Z subtractInt upper lower)) ∧
    ((zeroZ ≤Z lower) ∧
     (lower ≤Z j₁) ∧
     (j₁ ≤Z lengthZ after-swap))) ∧
   AfterLeftRecursion original after-swap lower j₁ upper)

FinishResult :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Set
FinishResult original current lower upper j₁ =
  (((zeroZ ≤Z lower) ∧ (lower <Z lengthZ current)) ∧
   ((zeroZ ≤Z j₁) ∧ (j₁ <Z lengthZ current))) ∧
  FinishSwapContinuation original current lower upper j₁

LoopSwapContinuation :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Set
LoopSwapContinuation original current lower upper j i i₁ j₁ pivot =
  (after-swap : List Int) →
  length after-swap ≡ length current →
  arrayExchange current after-swap i₁ j₁ →
  ((zeroZ ≤Z subtractInt j i) ∧
   (subtractInt j₁ i₁ <Z subtractInt j i)) ∧
  ((lower ≤Z i₁) ∧ (i₁ <Z subtractInt upper oneZ)) ∧
  AllLeClosed after-swap lower i₁ pivot ∧
  ((lower <Z j₁) ∧ (j₁ ≤Z upper)) ∧
  AllGeHalfOpen after-swap j₁ upper pivot ∧
  permutSub' original after-swap (toNat lower) (toNat upper) ∧
  nthInt after-swap lower ≡ pivot

LoopSwapResult :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Set
LoopSwapResult original current lower upper j i i₁ j₁ pivot =
  (((zeroZ ≤Z i₁) ∧ (i₁ <Z lengthZ current)) ∧
   ((zeroZ ≤Z j₁) ∧ (j₁ <Z lengthZ current))) ∧
  LoopSwapContinuation
    original
    current
    lower
    upper
    j
    i
    i₁
    j₁
    pivot

JProgress :
  List Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Set
JProgress current lower upper j j₁ pivot =
  ((zeroZ ≤Z j₁) ∧
   (subtractInt j₁ oneZ <Z j₁)) ∧
  ((lower ≤Z subtractInt j₁ oneZ) ∧
   (subtractInt j₁ oneZ <Z j)) ∧
  AllGeOpen current (subtractInt j₁ oneZ) upper pivot

J1Result :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Set
J1Result original current lower upper j i i₁ j₁ pivot =
  ((zeroZ ≤Z j₁) ∧ (j₁ <Z lengthZ current)) ∧
  IfSet
    (intLess pivot (nthInt current j₁))
    (IfSet
      (intEqual j₁ lower)
      (IfSet
        (intLessOrEqual j₁ i₁)
        (FinishResult original current lower upper j₁)
        (LoopSwapResult
          original
          current
          lower
          upper
          j
          i
          i₁
          j₁
          pivot))
      (JProgress current lower upper j j₁ pivot))
    (IfSet
      (intLessOrEqual j₁ i₁)
      (FinishResult original current lower upper j₁)
      (LoopSwapResult
        original
        current
        lower
        upper
        j
        i
        i₁
        j₁
        pivot))

AllJ1 :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Set
AllJ1 original current lower upper j i i₁ pivot =
  (j₁ : Int) →
  (((lower ≤Z j₁) ∧ (j₁ <Z j)) ∧
   AllGeOpen current j₁ upper pivot) →
  J1Result original current lower upper j i i₁ j₁ pivot

JScan :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Set
JScan original current lower upper j i i₁ pivot =
  (((lower ≤Z subtractInt j oneZ) ∧
    (subtractInt j oneZ <Z j)) ∧
   AllGeOpen current (subtractInt j oneZ) upper pivot) ∧
  AllJ1 original current lower upper j i i₁ pivot

IProgress :
  List Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Set
IProgress current lower upper i i₁ pivot =
  ((zeroZ ≤Z subtractInt upper i₁) ∧
   (subtractInt upper (addInt i₁ oneZ)
     <Z subtractInt upper i₁)) ∧
  ((i <Z addInt i₁ oneZ) ∧
   (addInt i₁ oneZ <Z upper)) ∧
  AllLeHalfOpen current lower (addInt i₁ oneZ) pivot

I1Result :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Set
I1Result original current lower upper j i i₁ pivot =
  ((zeroZ ≤Z i₁) ∧ (i₁ <Z lengthZ current)) ∧
  IfSet
    (intLess (nthInt current i₁) pivot)
    (IfSet
      (intEqual i₁ (subtractInt upper oneZ))
      (JScan original current lower upper j i i₁ pivot)
      (IProgress current lower upper i i₁ pivot))
    (JScan original current lower upper j i i₁ pivot)

AllI1 :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Set
AllI1 original current lower upper j i pivot =
  (i₁ : Int) →
  (((i <Z i₁) ∧ (i₁ <Z upper)) ∧
   AllLeHalfOpen current lower i₁ pivot) →
  I1Result original current lower upper j i i₁ pivot

LoopStateResult :
  List Int →
  List Int →
  Int →
  Int →
  Int →
  Int →
  Int →
  Set
LoopStateResult original current lower upper j i pivot =
  (((i <Z addInt i oneZ) ∧
    (addInt i oneZ <Z upper)) ∧
   AllLeHalfOpen current lower (addInt i oneZ) pivot) ∧
  AllI1 original current lower upper j i pivot

AllLoopStates :
  List Int →
  Int →
  Int →
  Int →
  Set
AllLoopStates original lower upper pivot =
  (j i : Int) →
  (current : List Int) →
  length current ≡ length original →
  LoopInvariant original current lower upper j i pivot →
  LoopStateResult original current lower upper j i pivot

RecursiveBranch : List Int → Int → Int → Set
RecursiveBranch array lower upper =
  let pivot = nthInt array lower
  in
  ((zeroZ ≤Z lower) ∧ (lower <Z lengthZ array)) ∧
  (LoopInvariant
     array
     array
     lower
     upper
     upper
     lower
     pivot ∧
   AllLoopStates array lower upper pivot)

quick-rec'vc : Set
quick-rec'vc =
  (lower upper : Int) →
  (array : List Int) →
  zeroZ ≤Z lower →
  lower ≤Z upper →
  upper ≤Z lengthZ array →
  IfSet
    (intLessOrEqual upper (addInt lower oneZ))
    (sortedSub1 array lower upper ∧
     permutSub'
       array
       array
       (toNat lower)
       (toNat upper))
    (RecursiveBranch array lower upper)
