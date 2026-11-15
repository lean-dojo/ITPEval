-- Statement-only formalization of VERINA corpus artifact verina_basic_104,
-- catalog title "update_map": a deterministic association-list map update
-- gives the second map priority, sorts the resulting entries by integer key,
-- and is connected to its full correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic104 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infix 4 _∈_

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

data IsTrue : Bool → Set where
  true-witness : IsTrue true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

boolNot : Bool → Bool
boolNot true = false
boolNot false = true

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

IntLessOrEqual : Int → Int → Set
IntLessOrEqual x y = IsTrue (intLessOrEqual x y)

record Pair (A B : Set) : Set where
  constructor pair
  field
    pairFirst : A
    pairSecond : B

open Pair public

record Map (K V : Set) : Set where
  constructor map
  field
    entries : List (Pair K V)

open Map public

empty : {K V : Set} → Map K V
empty = map []

data _∈_ {A : Set} (x : A) : List A → Set where
  here : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

data NoDuplicates {A : Set} : List A → Set where
  noDuplicatesNil : NoDuplicates []
  noDuplicatesCons :
    {x : A} {xs : List A} →
    Not (x ∈ xs) →
    NoDuplicates xs →
    NoDuplicates (x ∷ xs)

keys : {V : Set} → List (Pair Int V) → List Int
keys [] = []
keys (entry ∷ rest) =
  pairFirst entry ∷ keys rest

All : {A : Set} → (A → Set) → List A → Set
All predicate [] = Top
All predicate (x ∷ xs) =
  predicate x ∧ All predicate xs

Pairwise :
  {A : Set} → (A → A → Set) → List A → Set
Pairwise relation [] = Top
Pairwise relation (x ∷ xs) =
  All (relation x) xs ∧ Pairwise relation xs

filterNotKey :
  Int → List (Pair Int Int) → List (Pair Int Int)
filterNotKey key [] = []
filterNotKey key (entry ∷ rest) =
  if boolNot (intEqual (pairFirst entry) key)
  then entry ∷ filterNotKey key rest
  else filterNotKey key rest

appendList : {A : Set} → List A → List A → List A
appendList [] ys = ys
appendList (x ∷ xs) ys = x ∷ appendList xs ys

insert :
  Map Int Int → Int → Int → Map Int Int
insert m key value =
  map
    (appendList
      (filterNotKey key (entries m))
      (pair key value ∷ []))

foldLeft :
  {A B : Set} → (A → B → A) → A → List B → A
foldLeft step accumulator [] = accumulator
foldLeft step accumulator (x ∷ xs) =
  foldLeft step (step accumulator x) xs

insertEntry :
  Map Int Int → Pair Int Int → Map Int Int
insertEntry accumulator entry =
  insert accumulator (pairFirst entry) (pairSecond entry)

insertSorted :
  Pair Int Int →
  List (Pair Int Int) →
  List (Pair Int Int)
insertSorted entry [] = entry ∷ []
insertSorted entry (current ∷ rest) =
  if intLessOrEqual (pairFirst entry) (pairFirst current)
  then (entry ∷ current ∷ rest)
  else (current ∷ insertSorted entry rest)

sortEntries :
  List (Pair Int Int) → List (Pair Int Int)
sortEntries [] = []
sortEntries (entry ∷ rest) =
  insertSorted entry (sortEntries rest)

lookup :
  Map Int Int → Int → Maybe Int
lookup m key = findInEntries (entries m) key
  where
  findInEntries :
    List (Pair Int Int) → Int → Maybe Int
  findInEntries [] sought = nothing
  findInEntries (entry ∷ rest) sought =
    if intEqual (pairFirst entry) sought
    then just (pairSecond entry)
    else findInEntries rest sought

update-map-precond :
  Map Int Int → Map Int Int → Set
update-map-precond m1 m2 =
  NoDuplicates (keys (entries m1)) ∧
  NoDuplicates (keys (entries m2))

update-map :
  (m1 m2 : Map Int Int) →
  update-map-precond m1 m2 →
  Map Int Int
update-map m1 m2 h-precond =
  let updated =
        foldLeft insertEntry m1 (entries m2)
  in map (sortEntries (entries updated))

m1-entry-condition :
  Map Int Int →
  Map Int Int →
  Pair Int Int →
  Set
m1-entry-condition m2 result entry
  with lookup m2 (pairFirst entry)
... | just value = Top
... | nothing =
  lookup result (pairFirst entry) ≡ just (pairSecond entry)

result-entry-from-lookups :
  Pair Int Int →
  Maybe Int →
  Maybe Int →
  Set
result-entry-from-lookups entry (just oldValue) (just newValue) =
  pairSecond entry ≡ newValue
result-entry-from-lookups entry (just oldValue) nothing =
  pairSecond entry ≡ oldValue
result-entry-from-lookups entry nothing maybeNewValue =
  maybeNewValue ≡ just (pairSecond entry)

result-entry-condition :
  Map Int Int →
  Map Int Int →
  Pair Int Int →
  Set
result-entry-condition m1 m2 entry =
  result-entry-from-lookups
    entry
    (lookup m1 (pairFirst entry))
    (lookup m2 (pairFirst entry))

entriesOrdered :
  Pair Int Int → Pair Int Int → Set
entriesOrdered firstEntry secondEntry =
  IntLessOrEqual
    (pairFirst firstEntry)
    (pairFirst secondEntry)

update-map-postcond :
  (m1 m2 result : Map Int Int) →
  update-map-precond m1 m2 →
  Set
update-map-postcond m1 m2 result h-precond =
  Pairwise entriesOrdered (entries result) ∧
  All
    (λ entry →
      lookup result (pairFirst entry) ≡
      just (pairSecond entry))
    (entries m2) ∧
  All
    (m1-entry-condition m2 result)
    (entries m1) ∧
  All
    (result-entry-condition m1 m2)
    (entries result)

update-map-spec-satisfied : Set
update-map-spec-satisfied =
  (m1 m2 : Map Int Int) →
  (h-precond : update-map-precond m1 m2) →
  update-map-postcond
    m1
    m2
    (update-map m1 m2 h-precond)
    h-precond
