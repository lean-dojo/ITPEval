-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2021_lexicographic_permutations_1_Top_permutqtvc: the
-- verification condition for enumerating every integer-sequence permutation
-- exactly once in strict lexicographic order. This file contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2021LexicographicPermutations1TopPermutVC where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_ _∈S_ _⊆S_
infixr 5 _++_
infixr 3 _∧_
infixr 2 _∨_
infix 1 _↔_

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

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

boolNot : Bool → Bool
boolNot false = true
boolNot true = false

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

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

snoc : {A : Set} → List A → A → List A
snoc xs x = xs ++ (x ∷ [])

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

nthInt : List Int → Int → Int
nthInt xs index = nthDefault zeroZ (toNat index) xs

nthSequence : List (List Int) → Int → List Int
nthSequence sequences index =
  nthDefault [] (toNat index) sequences

sequenceEqual : List Int → List Int → Bool
sequenceEqual [] [] = true
sequenceEqual [] (_ ∷ _) = false
sequenceEqual (_ ∷ _) [] = false
sequenceEqual (x ∷ xs) (y ∷ ys) with intEqual x y
... | true = sequenceEqual xs ys
... | false = false

memberSequence : List Int → List (List Int) → Bool
memberSequence sought [] = false
memberSequence sought (candidate ∷ rest)
  with sequenceEqual sought candidate
... | true = true
... | false = memberSequence sought rest

insertUnique :
  List Int →
  List (List Int) →
  List (List Int)
insertUnique sequence sequences with memberSequence sequence sequences
... | true = sequences
... | false = sequence ∷ sequences

normalizeSet :
  List (List Int) →
  List (List Int)
normalizeSet [] = []
normalizeSet (sequence ∷ sequences) =
  insertUnique sequence (normalizeSet sequences)

FiniteSet : Set
FiniteSet = List (List Int)

_∈S_ : List Int → FiniteSet → Set
sequence ∈S set = memberSequence sequence set ≡ true

_⊆S_ : FiniteSet → FiniteSet → Set
leftSet ⊆S rightSet =
  (sequence : List Int) →
  sequence ∈S leftSet →
  sequence ∈S rightSet

insertSet : List Int → FiniteSet → FiniteSet
insertSet sequence set = sequence ∷ set

cardinal : FiniteSet → Int
cardinal set = lengthZ (normalizeSet set)

countInt : Int → List Int → Nat
countInt value [] = zero
countInt value (x ∷ xs) with intEqual value x
... | true = suc (countInt value xs)
... | false = countInt value xs

occAll : Int → List Int → Int
occAll value sequence = pos (countInt value sequence)

record SequenceModel : Set where
  field
    toSeq : List Int → List Int
    toSeq-length :
      (array : List Int) →
      length (toSeq array) ≡ length array
    toSeq-index :
      (array : List Int) →
      (index : Int) →
      zeroZ ≤Z index →
      index <Z lengthZ (toSeq array) →
      nthInt (toSeq array) index ≡ nthInt array index

open SequenceModel

IsPermutationOf :
  SequenceModel →
  List Int →
  List Int →
  Set
IsPermutationOf model permutation original =
  length permutation ≡ length original
  ∧ ((value : Int) →
      occAll value permutation ≡ occAll value original)

LexLess : List Int → List Int → Set
LexLess leftSequence rightSequence =
  (length leftSequence ≡ length rightSequence
   ∧ zeroZ <Z lengthZ rightSequence)
  ∧
  Exists Int
    (λ index →
      (zeroZ ≤Z index ∧ index <Z lengthZ leftSequence)
      ∧
      ((prefixIndex : Int) →
        (zeroZ ≤Z prefixIndex ∧ prefixIndex <Z index) →
        nthInt leftSequence prefixIndex ≡
          nthInt rightSequence prefixIndex)
      ∧ nthInt leftSequence index <Z
          nthInt rightSequence index)

record PermutationUniverse
  (model : SequenceModel) :
  Set where

  field
    allPermutations : List Int → FiniteSet
    allPermutations-spec :
      (permutation original : List Int) →
      IsPermutationOf model permutation original →
      permutation ∈S allPermutations original

open PermutationUniverse

SequenceCopySpec : List Int → List Int → Set
SequenceCopySpec sequence array =
  length sequence ≡ length array
  ∧
  ((index : Int) →
    (zeroZ ≤Z index ∧ index <Z lengthZ sequence) →
    nthInt sequence index ≡ nthInt array index)

SortedArray : List Int → Set
SortedArray array =
  (leftIndex rightIndex : Int) →
  (zeroZ ≤Z leftIndex
   ∧ leftIndex ≤Z rightIndex
   ∧ rightIndex <Z lengthZ array) →
  nthInt array leftIndex ≤Z nthInt array rightIndex

SnocSpec :
  List (List Int) →
  List (List Int) →
  List Int →
  Set
SnocSpec before after appended =
  lengthZ after ≡ addInt oneZ (lengthZ before)
  ∧ nthSequence after (lengthZ before) ≡ appended
  ∧
  ((index : Int) →
    (zeroZ ≤Z index ∧ index <Z lengthZ before) →
    nthSequence after index ≡ nthSequence before index)

AllResultPermutations :
  SequenceModel →
  List Int →
  List (List Int) →
  Set
AllResultPermutations model original result =
  (index : Int) →
  (zeroZ ≤Z index ∧ index <Z lengthZ result) →
  IsPermutationOf model (nthSequence result index) original

StrictlyLexicographic :
  List (List Int) →
  Set
StrictlyLexicographic result =
  (leftIndex rightIndex : Int) →
  (zeroZ ≤Z leftIndex
   ∧ leftIndex <Z rightIndex
   ∧ rightIndex <Z lengthZ result) →
  LexLess
    (nthSequence result leftIndex)
    (nthSequence result rightIndex)

AllBeforeLast :
  SequenceModel →
  List Int →
  List Int →
  List (List Int) →
  Set
AllBeforeLast model original lastSequence result =
  (permutation : List Int) →
  IsPermutationOf model permutation original →
  LexLess permutation lastSequence →
  Exists Int
    (λ index →
      (zeroZ ≤Z index
       ∧ index <Z subtractInt (lengthZ result) oneZ)
      ∧ nthSequence result index ≡ permutation)

SetEnumeratesResult :
  FiniteSet →
  List (List Int) →
  Set
SetEnumeratesResult set result =
  (permutation : List Int) →
  (permutation ∈S set)
  ↔
  Exists Int
    (λ index →
      (zeroZ ≤Z index ∧ index <Z lengthZ result)
      ∧ nthSequence result index ≡ permutation)

EnumerationStateWithLast :
  SequenceModel →
  List Int →
  FiniteSet →
  List Int →
  List (List Int) →
  List Int →
  FiniteSet →
  Set
EnumerationStateWithLast
  model original allSet currentArray result lastSnapshot resultSet =
  zeroZ <Z lengthZ result
  ∧ IsPermutationOf model (toSeq model currentArray) original
  ∧ AllResultPermutations model original result
  ∧
  (lastSnapshot ≡
     nthSequence result (subtractInt (lengthZ result) oneZ)
   ∧
   nthSequence result (subtractInt (lengthZ result) oneZ) ≡
     toSeq model currentArray)
  ∧ IsPermutationOf model lastSnapshot original
  ∧ StrictlyLexicographic result
  ∧ AllBeforeLast model original lastSnapshot result
  ∧ SetEnumeratesResult resultSet result
  ∧ resultSet ⊆S allSet

LoopInvariant :
  SequenceModel →
  List Int →
  FiniteSet →
  List Int →
  List (List Int) →
  FiniteSet →
  Set
LoopInvariant model original allSet currentArray result resultSet =
  let lastSequence =
        nthSequence result (subtractInt (lengthZ result) oneZ)
  in
  zeroZ <Z lengthZ result
  ∧ IsPermutationOf model (toSeq model currentArray) original
  ∧ AllResultPermutations model original result
  ∧ lastSequence ≡ toSeq model currentArray
  ∧ IsPermutationOf model lastSequence original
  ∧ StrictlyLexicographic result
  ∧ AllBeforeLast model original lastSequence result
  ∧ SetEnumeratesResult resultSet result
  ∧ resultSet ⊆S allSet

NextResultContract :
  SequenceModel →
  List Int →
  List Int →
  List Int →
  Bool →
  Set
NextResultContract model original previousArray nextArray flag =
  IsPermutationOf model (toSeq model nextArray) original
  ∧
  (boolNot flag ≡ true →
    (index : Int) →
    (zeroZ ≤Z index ∧ index <Z lengthZ nextArray) →
    nthInt nextArray index ≡ nthInt previousArray index)
  ∧
  (boolNot flag ≡ true →
    (permutation : List Int) →
    IsPermutationOf model permutation original →
    Not (LexLess (toSeq model nextArray) permutation))
  ∧
  (flag ≡ true →
    LexLess
      (toSeq model previousArray)
      (toSeq model nextArray))
  ∧
  (flag ≡ true →
    (permutation : List Int) →
    IsPermutationOf model permutation original →
    Not
      (LexLess (toSeq model previousArray) permutation
       ∧ LexLess permutation (toSeq model nextArray)))

VariantDecrease :
  FiniteSet →
  FiniteSet →
  List Int →
  Set
VariantDecrease allSet resultSet added =
  zeroZ ≤Z subtractInt (cardinal allSet) (cardinal resultSet)
  ∧
  subtractInt
    (cardinal allSet)
    (cardinal (insertSet added resultSet))
  <Z
  subtractInt (cardinal allSet) (cardinal resultSet)

SuccessBranch :
  SequenceModel →
  List Int →
  FiniteSet →
  List Int →
  List Int →
  List (List Int) →
  FiniteSet →
  Set
SuccessBranch
  model original allSet nextArray previousArray result resultSet =
  let nextSequence = toSeq model nextArray
  in
  SequenceCopySpec nextSequence nextArray →
  let extendedResult = snoc result nextSequence
  in
  SnocSpec result extendedResult nextSequence →
  let lastSnapshot = toSeq model nextArray
  in
  SequenceCopySpec lastSnapshot nextArray →
  let insertedSequence = toSeq model nextArray
  in
  SequenceCopySpec insertedSequence nextArray →
  VariantDecrease allSet resultSet insertedSequence
  ∧
  EnumerationStateWithLast
    model
    original
    allSet
    nextArray
    extendedResult
    lastSnapshot
    (insertSet insertedSequence resultSet)

FinalResult :
  SequenceModel →
  List Int →
  List (List Int) →
  Set
FinalResult model originalSequence result =
  AllResultPermutations
    model
    originalSequence
    result
  ∧ StrictlyLexicographic result
  ∧
  ((permutation : List Int) →
    IsPermutationOf
      model
      permutation
      originalSequence →
    Exists Int
      (λ index →
        (zeroZ ≤Z index ∧ index <Z lengthZ result)
        ∧ nthSequence result index ≡ permutation))

LoopStep :
  SequenceModel →
  List Int →
  FiniteSet →
  List Int →
  List Int →
  List (List Int) →
  FiniteSet →
  Set
LoopStep
  model original allSet previousArray nextArray result resultSet =
  (flag : Bool) →
  NextResultContract model original previousArray nextArray flag →
  IfSet
    flag
    (SuccessBranch
      model
      original
      allSet
      nextArray
      previousArray
      result
      resultSet)
    (FinalResult model original result)

LoopObligation :
  SequenceModel →
  List Int →
  FiniteSet →
  List Int →
  Set
LoopObligation model original allSet sortedArray =
  (resultSet : FiniteSet) →
  (result : List (List Int)) →
  (currentArray : List Int) →
  length currentArray ≡ length sortedArray →
  LoopInvariant
    model
    original
    allSet
    currentArray
    result
    resultSet →
  (length currentArray ≡ length original
   ∧ IsPermutationOf
      model
      (toSeq model currentArray)
      original)
  ∧
  ((nextArray : List Int) →
    length nextArray ≡ length currentArray →
    LoopStep
      model
      original
      allSet
      currentArray
      nextArray
      result
      resultSet)

AfterSort :
  (model : SequenceModel) →
  PermutationUniverse model →
  List Int →
  List Int →
  FiniteSet →
  Set
AfterSort model universe originalArray sortedArray allSet =
  length sortedArray ≡ length originalArray →
  (SortedArray sortedArray
   ∧ IsPermutationOf
      model
      (toSeq model sortedArray)
      (toSeq model originalArray)) →
  let firstSequence = toSeq model sortedArray
  in
  SequenceCopySpec firstSequence sortedArray →
  let emptyResult : List (List Int)
      emptyResult = []
      initialResult = snoc emptyResult firstSequence
  in
  SnocSpec emptyResult initialResult firstSequence →
  let lastSnapshot = toSeq model sortedArray
  in
  SequenceCopySpec lastSnapshot sortedArray →
  let insertedSequence = toSeq model sortedArray
  in
  SequenceCopySpec insertedSequence sortedArray →
  let initialSet = insertSet insertedSequence []
  in
  EnumerationStateWithLast
    model
    (toSeq model originalArray)
    allSet
    sortedArray
    initialResult
    lastSnapshot
    initialSet
  ∧
  LoopObligation
    model
    (toSeq model originalArray)
    allSet
    sortedArray

PermutVC :
  (model : SequenceModel) →
  (universe : PermutationUniverse model) →
  List Int →
  Set
PermutVC model universe originalArray =
  let originalSequence = toSeq model originalArray
  in
  SequenceCopySpec originalSequence originalArray →
  let allSet = allPermutations universe originalSequence
  in
  ((permutation : List Int) →
    IsPermutationOf model permutation originalSequence →
    permutation ∈S allSet) →
  ((sortedArray : List Int) →
    AfterSort
      model
      universe
      originalArray
      sortedArray
      allSet)

permut'vc : Set
permut'vc =
  (model : SequenceModel) →
  (universe : PermutationUniverse model) →
  (array : List Int) →
  PermutVC model universe array
