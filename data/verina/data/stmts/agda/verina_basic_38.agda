-- Statement-only formalization of VERINA corpus artifact verina_basic_38,
-- catalog title "allCharactersSame": a deterministic string program checks
-- whether every character equals the first and is connected to its pairwise
-- equality and differing-character correctness contract. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module VerinaBasic38 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Char using
  (Char; primCharEquality; primNatToChar)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (zero)
open import Agda.Builtin.String using (String; primStringToList)

infixr 3 _∧_

record Top : Set where
  constructor top

data Empty : Set where

Not : Set → Set
Not A = A → Empty

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

notBool : Bool → Bool
notBool true = false
notBool false = true

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

anyList : {A : Set} → (A → Bool) → List A → Bool
anyList predicate [] = false
anyList predicate (x ∷ xs) =
  if predicate x
  then true
  else anyList predicate xs

headDefault : {A : Set} → A → List A → A
headDefault default [] = default
headDefault default (x ∷ xs) = x

All : {A : Set} → (A → Set) → List A → Set
All predicate [] = Top
All predicate (x ∷ xs) =
  predicate x ∧ All predicate xs

Pairwise :
  {A : Set} →
  (A → A → Set) →
  List A →
  Set
Pairwise relation [] = Top
Pairwise relation (x ∷ xs) =
  All (relation x) xs ∧ Pairwise relation xs

nullChar : Char
nullChar = primNatToChar zero

allCharactersSame-precond : String → Set
allCharactersSame-precond s = Top

allCharactersSame :
  (s : String) →
  allCharactersSame-precond s →
  Bool
allCharactersSame s h-precond with primStringToList s
... | [] = true
... | c ∷ cs =
  allList (λ x → primCharEquality x c) cs

allCharactersSame-postcond :
  (s : String) →
  (result : Bool) →
  allCharactersSame-precond s →
  Set
allCharactersSame-postcond s result h-precond =
  let characters = primStringToList s
  in
    (IsTrue result →
      Pairwise (λ x y → x ≡ y) characters) ∧
    (Not (IsTrue result) →
      Not (characters ≡ []) ∧
      IsTrue
        (anyList
          (λ x →
            notBool
              (primCharEquality
                x
                (headDefault nullChar characters)))
          characters))

allCharactersSame-spec-satisfied : Set
allCharactersSame-spec-satisfied =
  (s : String) →
  (h-precond : allCharactersSame-precond s) →
  allCharactersSame-postcond
    s
    (allCharactersSame s h-precond)
    h-precond
