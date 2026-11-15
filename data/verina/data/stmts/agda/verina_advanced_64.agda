-- Statement-only formalization of VERINA corpus artifact verina_advanced_64,
-- catalog title "removeElement": a deterministic recursive list program removes
-- every occurrence of a target natural number and is connected to its
-- indexwise filtered-list contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced64 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_

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

filterList : {A : Set} → (A → Bool) → List A → List A
filterList predicate [] = []
filterList predicate (x ∷ xs) =
  if predicate x
  then x ∷ filterList predicate xs
  else filterList predicate xs

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

removeElement-precond : List Nat → Nat → Set
removeElement-precond lst target = Top

removeElement-helper : List Nat → Nat → List Nat
removeElement-helper [] target = []
removeElement-helper (x ∷ xs) target =
  let rest = removeElement-helper xs target
  in
    if natEqual x target
    then rest
    else (x ∷ rest)

removeElement :
  (lst : List Nat) →
  (target : Nat) →
  removeElement-precond lst target →
  List Nat
removeElement lst target h-precond =
  removeElement-helper lst target

record IndexedNat : Set where
  constructor indexed
  field
    indexedValue : Nat
    indexedPosition : Nat

open IndexedNat public

zipIdxFrom : Nat → List Nat → List IndexedNat
zipIdxFrom position [] = []
zipIdxFrom position (x ∷ xs) =
  indexed x position ∷ zipIdxFrom (suc position) xs

zipIdx : List Nat → List IndexedNat
zipIdx values = zipIdxFrom zero values

listGetMaybe : List Nat → Nat → Maybe Nat
listGetMaybe [] position = nothing
listGetMaybe (x ∷ xs) zero = just x
listGetMaybe (x ∷ xs) (suc position) = listGetMaybe xs position

indexedMatches : List Nat → IndexedNat → Bool
indexedMatches expected entry
  with listGetMaybe expected (indexedPosition entry)
... | nothing = false
... | just expected-value =
  natEqual (indexedValue entry) expected-value

removeElement-postcond :
  (lst : List Nat) →
  (target : Nat) →
  (result : List Nat) →
  removeElement-precond lst target →
  Set
removeElement-postcond lst target result h-precond =
  let filtered =
        filterList
          (λ x → boolNot (natEqual x target))
          lst
  in
    IsTrue
      (allList
        (indexedMatches filtered)
        (zipIdx result)) ∧
    (listLength result ≡ listLength filtered)

removeElement-spec-satisfied : Set
removeElement-spec-satisfied =
  (lst : List Nat) →
  (target : Nat) →
  (h-precond : removeElement-precond lst target) →
  removeElement-postcond
    lst
    target
    (removeElement lst target h-precond)
    h-precond
