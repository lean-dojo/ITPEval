-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/sumrange_CumulativeTree_tree_of_arrayqtvc: the cumulative range-sum
-- tree construction verification condition, including midpoint recursive-call
-- obligations and preservation of the tree invariant. This file contains no proof.

{-# OPTIONS --safe #-}

module sumrange_CumulativeTree_tree_of_arrayqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

data Bottom : Set where

Not : Set → Set
Not A = A → Bottom

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record Exists {A : Set} (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    evidence : P value

IfSet : Bool → Set → Set → Set
IfSet true whenTrue whenFalse = whenTrue
IfSet false whenTrue whenFalse = whenFalse

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

negateInt : Int → Int
negateInt (pos n) = negativeNat n
negateInt (negsuc n) = pos (suc n)

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

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

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

sumList : List Int → Int
sumList [] = pos zero
sumList (x ∷ xs) = addInt x (sumList xs)

sumBetween : List Int → Int → Int → Int
sumBetween values i j =
  sumList
    (take
      (natSubtract (toNat j) (toNat i))
      (drop (toNat i) values))

zeroZ oneZ twoZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))

nthInt : List Int → Int → Int
nthInt values index =
  nthDefault zeroZ (toNat index) values

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

recursiveCallObligations :
  List Int → Int → Int → Set
recursiveCallObligations values i j =
  let middle = computerDivideByTwo (addInt i j)
      width = subtractInt j i
  in
  ((zeroZ ≤Z width) ∧
   (subtractInt middle i <Z width)) ∧
  ((zeroZ ≤Z i) ∧
   (i <Z middle) ∧
   (middle ≤Z pos (length values))) ∧
  ((leftTree : Tree) →
    isTreeFor leftTree values i middle →
    ((zeroZ ≤Z width) ∧
     (subtractInt j middle <Z width)) ∧
    ((zeroZ ≤Z middle) ∧
     (middle <Z j) ∧
     (j ≤Z pos (length values))))

constructionResult :
  List Int → Int → Int → Tree → Set
constructionResult values i j result =
  let next = addInt i oneZ
      middle = computerDivideByTwo (addInt i j)
  in
  IfSet
    (intEqual next j)
    (result ≡ leaf (indexes i j (nthInt values i)))
    (Exists
      (λ leftTree →
        isTreeFor leftTree values i middle ∧
        Exists
          (λ rightTree →
            isTreeFor rightTree values middle j ∧
            (result ≡
              node
                (indexes
                  i
                  j
                  (addInt
                    (isum (indexesOf leftTree))
                    (isum (indexesOf rightTree))))
                leftTree
                rightTree))))

TreeOfArrayVC : Set
TreeOfArrayVC =
  (i j : Int) →
  (values : List Int) →
  zeroZ ≤Z i →
  i <Z j →
  j ≤Z pos (length values) →
  let next = addInt i oneZ
  in
  (IfSet
    (intEqual next j)
    ((zeroZ ≤Z i) ∧ (i <Z pos (length values)))
    (Not (twoZ ≡ zeroZ) ∧
     recursiveCallObligations values i j))
  ∧
  ((result : Tree) →
    constructionResult values i j result →
    isTreeFor result values i j)

sumrange-CumulativeTree-tree-of-arrayqtvc : Set
sumrange-CumulativeTree-tree-of-arrayqtvc =
  TreeOfArrayVC
