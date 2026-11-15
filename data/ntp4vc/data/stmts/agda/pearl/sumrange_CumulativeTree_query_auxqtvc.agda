-- Statement-only formalization of NTP4VC corpus artifact
-- pearl/sumrange_CumulativeTree_query_auxqtvc: the cumulative-tree range-sum
-- query auxiliary verification condition, including recursive-call
-- obligations and the final half-open range-sum result relation.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module sumrange_CumulativeTree_query_auxqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_
infixr 2 _∨_

data Bottom : Set where

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

record Exists {A : Set} (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    evidence : P value

IfSet : Bool → Set → Set → Set
IfSet true whenTrue whenFalse = whenTrue
IfSet false whenTrue whenFalse = whenFalse

ifBool : {A : Set} → Bool → A → A → A
ifBool true whenTrue whenFalse = whenTrue
ifBool false whenTrue whenFalse = whenFalse

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

boolEqual : Bool → Bool → Bool
boolEqual false false = true
boolEqual false true = false
boolEqual true false = false
boolEqual true true = true

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

negativeNat : Nat → Int
negativeNat zero = pos zero
negativeNat (suc n) = negsuc n

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

half : Nat → Nat
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

computerDivideByTwo : Int → Int
computerDivideByTwo (pos n) = pos (half n)
computerDivideByTwo (negsuc n) = negativeNat (half (suc n))

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

natSubtract : Nat → Nat → Nat
natSubtract n zero = n
natSubtract zero (suc _) = zero
natSubtract (suc m) (suc n) = natSubtract m n

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

drop : {A : Set} → Nat → List A → List A
drop zero xs = xs
drop (suc _) [] = []
drop (suc n) (_ ∷ xs) = drop n xs

take : {A : Set} → Nat → List A → List A
take zero xs = []
take (suc _) [] = []
take (suc n) (x ∷ xs) = x ∷ take n xs

sumList : List Int → Int
sumList [] = pos zero
sumList (x ∷ xs) = addInt x (sumList xs)

sumBetween : List Int → Int → Int → Int
sumBetween values i j =
  sumList
    (take
      (natSubtract (toNat j) (toNat i))
      (drop (toNat i) values))

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

record Indexes : Set where
  constructor indexes
  field
    low  : Int
    high : Int
    isum : Int

open Indexes

data Tree : Set where
  leaf : Indexes → Tree
  node : Indexes → Tree → Tree → Tree

indexesOf : Tree → Indexes
indexesOf (leaf ind) = ind
indexesOf (node ind leftTree rightTree) = ind

isIndexesFor : Indexes → List Int → Int → Int → Set
isIndexesFor ind values i j =
  (low ind ≡ i) ∧
  (high ind ≡ j) ∧
  ((zeroZ ≤Z i) ∧
   (i <Z j) ∧
   (j ≤Z pos (length values))) ∧
  (isum ind ≡ sumBetween values i j)

isTreeFor : Tree → List Int → Int → Int → Set
isTreeFor (leaf ind) values i j =
  isIndexesFor ind values i j ∧
  (j ≡ addInt i oneZ)
isTreeFor (node ind leftTree rightTree) values i j =
  isIndexesFor ind values i j ∧
  (i ≡ low (indexesOf leftTree)) ∧
  (j ≡ high (indexesOf rightTree)) ∧
  let middle = high (indexesOf leftTree)
  in
  (middle ≡ low (indexesOf rightTree)) ∧
  ((i <Z middle) ∧ (middle <Z j)) ∧
  (middle ≡ computerDivideByTwo (addInt i j)) ∧
  isTreeFor leftTree values i middle ∧
  isTreeFor rightTree values middle j

isImmediateChild : Tree → Tree → Set
isImmediateChild (leaf _) child = Bottom
isImmediateChild (node _ leftTree rightTree) child =
  (leftTree ≡ child) ∨ (rightTree ≡ child)

callContext :
  Tree → Tree → List Int → Int → Int → Set
callContext wholeTree child values i j =
  isImmediateChild wholeTree child ∧
  isTreeFor
    child
    values
    (low (indexesOf child))
    (high (indexesOf child)) ∧
  (zeroZ ≤Z low (indexesOf child)) ∧
  (low (indexesOf child) ≤Z i) ∧
  (i <Z j) ∧
  (j ≤Z high (indexesOf child)) ∧
  (high (indexesOf child) ≤Z pos (length values))

nodeCallObligations :
  Indexes → Tree → Tree → List Int → Int → Int → Set
nodeCallObligations ind leftTree rightTree values i j =
  (branchCondition : Bool) →
  IfSet
    (intEqual i (low ind))
    (branchCondition ≡
      ifBool (intEqual j (high ind)) true false)
    (branchCondition ≡ false) →
  ((branchCondition ≡ true) → Bottom) →
  let wholeTree = node ind leftTree rightTree
      middle = high (indexesOf leftTree)
  in
  IfSet
    (intLessOrEqual j middle)
    (callContext wholeTree leftTree values i j)
    (IfSet
      (intLessOrEqual middle i)
      (callContext wholeTree rightTree values i j)
      (callContext wholeTree rightTree values middle j ∧
       callContext wholeTree leftTree values i middle))

callObligations : Tree → List Int → Int → Int → Set
callObligations (leaf ind) values i j = Top
callObligations (node ind leftTree rightTree) values i j =
  nodeCallObligations ind leftTree rightTree values i j

nodeFallbackResult :
  Tree → List Int → Int → Int → Int → Set
nodeFallbackResult leftTree values i j result =
  let middle = high (indexesOf leftTree)
  in
  IfSet
    (intLessOrEqual j middle)
    (result ≡ sumBetween values i j)
    (IfSet
      (intLessOrEqual middle i)
      (result ≡ sumBetween values i j)
      (result ≡
       addInt
         (sumBetween values i middle)
         (sumBetween values middle j)))

nodeBodyResult :
  Indexes → Tree → Tree → List Int → Int → Int → Int → Set
nodeBodyResult ind leftTree rightTree values i j result =
  Exists
    (λ branchCondition →
      IfSet
        (intEqual i (low ind))
        (branchCondition ≡
          ifBool (intEqual j (high ind)) true false)
        (branchCondition ≡ false) ∧
      IfSet
        (boolEqual branchCondition true)
        (result ≡ isum ind)
        (nodeFallbackResult leftTree values i j result))

queryBodyResult :
  Tree → List Int → Int → Int → Int → Set
queryBodyResult (leaf ind) values i j result =
  result ≡ isum ind
queryBodyResult (node ind leftTree rightTree) values i j result =
  nodeBodyResult ind leftTree rightTree values i j result

allResultsCorrect : Tree → List Int → Int → Int → Set
allResultsCorrect tree values i j =
  (result : Int) →
  queryBodyResult tree values i j result →
  result ≡ sumBetween values i j

QueryAuxVC : Set
QueryAuxVC =
  (tree : Tree) →
  (values : List Int) →
  (i j : Int) →
  isTreeFor
    tree
    values
    (low (indexesOf tree))
    (high (indexesOf tree)) →
  zeroZ ≤Z low (indexesOf tree) →
  low (indexesOf tree) ≤Z i →
  i <Z j →
  j ≤Z high (indexesOf tree) →
  high (indexesOf tree) ≤Z pos (length values) →
  callObligations tree values i j ∧
  allResultsCorrect tree values i j

sumrange-CumulativeTree-query-auxqtvc : Set
sumrange-CumulativeTree-query-auxqtvc =
  QueryAuxVC
