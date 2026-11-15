-- Statement-only formalization of VERINA corpus artifact verina_advanced_13,
-- catalog title "hasChordIntersection": a deterministic program decides
-- whether normalized chords have alternating endpoints on the circle.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced13 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infixr 3 _∧_
infix 4 _≤_ _<_
infixr 5 _&&_ _||_

data Empty : Set where

Not : Set → Set
Not A = A → Empty

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

data IsTrue : Bool → Set where
  true-witness : IsTrue true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

_&&_ : Bool → Bool → Bool
true && other = other
false && other = false

_||_ : Bool → Bool → Bool
true || other = true
false || other = other

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

one : Nat
one = suc zero

two : Nat
two = suc one

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

appendList : {A : Set} → List A → List A → List A
appendList [] ys = ys
appendList (x ∷ xs) ys = x ∷ appendList xs ys

flatMapList :
  {A B : Set} → (A → List B) → List A → List B
flatMapList f [] = []
flatMapList f (x ∷ xs) = appendList (f x) (flatMapList f xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) = nthDefault default n xs

firstEndpoint : List Nat → Nat
firstEndpoint chord = nthDefault zero zero chord

secondEndpoint : List Nat → Nat
secondEndpoint chord = nthDefault zero one chord

normalizeChord : List Nat → List Nat
normalizeChord chord =
  let a = firstEndpoint chord
      b = secondEndpoint chord
  in if natLess b a
     then (b ∷ a ∷ [])
     else (a ∷ b ∷ [])

allChordsValid : Nat → List (List Nat) → Bool
allChordsValid N [] = true
allChordsValid N (chord ∷ chords) =
  natEqual (listLength chord) two &&
  natLessOrEqual one (firstEndpoint chord) &&
  natLessOrEqual (firstEndpoint chord) (two * N) &&
  natLessOrEqual one (secondEndpoint chord) &&
  natLessOrEqual (secondEndpoint chord) (two * N) &&
  allChordsValid N chords

All : {A : Set} → (A → Set) → List A → Set
All predicate [] = Top
All predicate (x ∷ xs) = predicate x ∧ All predicate xs

data _∈_ {A : Set} (x : A) : List A → Set where
  here : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

NoDuplicates : List Nat → Set
NoDuplicates [] = Top
NoDuplicates (x ∷ xs) = Not (x ∈ xs) ∧ NoDuplicates xs

HasChordIntersection-precond :
  Nat → List (List Nat) → Set
HasChordIntersection-precond N chords =
  (two ≤ N) ∧
  ((listLength chords ≡ N) ∧
  ((IsTrue (allChordsValid N chords)) ∧
  (NoDuplicates (flatMapList (λ chord → chord) chords))))

dropWhileList :
  {A : Set} → (A → Bool) → List A → List A
dropWhileList predicate [] = []
dropWhileList predicate (x ∷ xs) =
  if predicate x
  then dropWhileList predicate xs
  else (x ∷ xs)

insertChord :
  List Nat → List (List Nat) → List (List Nat)
insertChord x [] = x ∷ []
insertChord x (y ∷ ys) =
  if natLess (firstEndpoint x) (firstEndpoint y)
  then (x ∷ y ∷ ys)
  else (y ∷ insertChord x ys)

sortChords : List (List Nat) → List (List Nat)
sortChords [] = []
sortChords (x ∷ xs) = insertChord x (sortChords xs)

checkIntersection :
  List (List Nat) → List (List Nat) → Bool
checkIntersection stack [] = false
checkIntersection stack (chord ∷ rest) =
  let a = firstEndpoint chord
      b = secondEndpoint chord
      newStack =
        dropWhileList
          (λ c → natLess (secondEndpoint c) a)
          stack
  in checkNewStack a b chord rest newStack
  where
  checkNewStack :
    Nat →
    Nat →
    List Nat →
    List (List Nat) →
    List (List Nat) →
    Bool
  checkNewStack a b chord rest [] =
    checkIntersection (chord ∷ []) rest
  checkNewStack a b chord rest (topChord ∷ stackTail) =
    if
      natLess a (secondEndpoint topChord) &&
      natLess (secondEndpoint topChord) b
    then true
    else checkIntersection (chord ∷ topChord ∷ stackTail) rest

hasChordIntersection :
  (N : Nat) →
  (chords : List (List Nat)) →
  HasChordIntersection-precond N chords →
  Bool
hasChordIntersection N chords h-precond =
  checkIntersection
    []
    (sortChords (mapList normalizeChord chords))

hasIntersection : List Nat → List Nat → Bool
hasIntersection chord1 chord2 =
  let a1 = firstEndpoint chord1
      b1 = secondEndpoint chord1
      a2 = firstEndpoint chord2
      b2 = secondEndpoint chord2
  in
    (natLess a1 a2 && natLess a2 b1 && natLess b1 b2) ||
    (natLess a2 a1 && natLess a1 b2 && natLess b2 b1)

anyList : {A : Set} → (A → Bool) → List A → Bool
anyList predicate [] = false
anyList predicate (x ∷ xs) =
  if predicate x then true else anyList predicate xs

checkAllPairs : List (List Nat) → Bool
checkAllPairs [] = false
checkAllPairs (x ∷ xs) =
  if anyList (hasIntersection x) xs
  then true
  else checkAllPairs xs

Pairwise :
  {A : Set} → (A → A → Set) → List A → Set
Pairwise relation [] = Top
Pairwise relation (x ∷ xs) =
  All (relation x) xs ∧ Pairwise relation xs

noIntersectionRelation :
  List Nat → List Nat → Set
noIntersectionRelation x y =
  IsTrue (notBool (hasIntersection x y))

anyIntersection : List (List Nat) → Bool
anyIntersection chords =
  anyList
    (λ x → anyList (λ y → hasIntersection x y) chords)
    chords

HasChordIntersection-postcond :
  (N : Nat) →
  (chords : List (List Nat)) →
  (result : Bool) →
  HasChordIntersection-precond N chords →
  Set
HasChordIntersection-postcond N chords result h-precond =
  let normalizedChords = mapList normalizeChord chords
  in
    (Pairwise noIntersectionRelation normalizedChords →
      Not (IsTrue result)) ∧
    (IsTrue (anyIntersection normalizedChords) →
      IsTrue result)

HasChordIntersection-spec-satisfied : Set
HasChordIntersection-spec-satisfied =
  (N : Nat) →
  (chords : List (List Nat)) →
  (h-precond : HasChordIntersection-precond N chords) →
  HasChordIntersection-postcond
    N
    chords
    (hasChordIntersection N chords h-precond)
    h-precond
