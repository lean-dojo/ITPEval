-- Statement-only formalization of VERINA corpus artifact verina_advanced_65,
-- catalog title "reverseString": a deterministic accumulator-based program
-- reverses a string's character list and is connected to its length-and-reversal
-- correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced65 where

open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using
  (String; primStringFromList; primStringToList)

infixr 3 _∧_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

reverseAux : {A : Set} → List A → List A → List A
reverseAux [] accumulator = accumulator
reverseAux (x ∷ xs) accumulator =
  reverseAux xs (x ∷ accumulator)

reverseList : {A : Set} → List A → List A
reverseList xs = reverseAux xs []

reverseString-precond : String → Set
reverseString-precond s = Top

reverseString :
  (s : String) →
  reverseString-precond s →
  String
reverseString s h-precond =
  primStringFromList
    (reverseAux (primStringToList s) [])

reverseString-postcond :
  (s : String) →
  (result : String) →
  reverseString-precond s →
  Set
reverseString-postcond s result h-precond =
  (listLength (primStringToList result) ≡
    listLength (primStringToList s)) ∧
  (primStringToList result ≡
    reverseList (primStringToList s))

reverseString-spec-satisfied : Set
reverseString-spec-satisfied =
  (s : String) →
  (h-precond : reverseString-precond s) →
  reverseString-postcond
    s
    (reverseString s h-precond)
    h-precond
