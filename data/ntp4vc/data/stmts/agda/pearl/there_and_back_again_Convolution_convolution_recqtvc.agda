-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/there_and_back_again_Convolution_convolution_recqtvc: the recursive
-- symbolic-convolution verification condition over an inhabited element type,
-- relating consumed input, reversed prefixes, paired output, and the
-- unconsumed suffix. This file contains no proof.

{-# OPTIONS --safe #-}

module there_and_back_again_Convolution_convolution_recqtvc where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)

infix 4 _≤_
infixr 5 _++_
infixr 4 _×_
infixr 3 _∧_

data ⊥ : Set where

record ⊤ : Set where
  constructor tt

record Inhabited (A : Set) : Set where
  constructor inhabited
  field
    witness : A

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

data _≤_ : Nat → Nat → Set where
  z≤n : {n : Nat} → zero ≤ n
  s≤s : {m n : Nat} → m ≤ n → suc m ≤ suc n

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ (x ∷ [])

zip : {A B : Set} → List A → List B → List (A × B)
zip [] _ = []
zip _ [] = []
zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ zip xs ys

TailMatches : {A : Set} → List A → List A → Set
TailMatches [] _ = ⊥
TailMatches (_ ∷ actualTail) expectedTail =
  actualTail ≡ expectedTail

NonEmpty : {A : Set} → List A → Set
NonEmpty [] = ⊥
NonEmpty (_ ∷ _) = ⊤

PrefixWitness :
  {A : Set} →
  List A →
  List A →
  List A →
  List (A × A) →
  Set
PrefixWitness y xs suffix pairs =
  Σ (List _) λ y₀ →
    y ≡ y₀ ++ suffix
    ∧ length y₀ ≡ length xs
    ∧ pairs ≡ zip xs (reverse y₀)

RecursiveCallObligation :
  {A : Set} →
  List A →
  List A →
  Set
RecursiveCallObligation [] y = ⊤
RecursiveCallObligation (x₀ ∷ xs) y =
  (TailMatches (x₀ ∷ xs) xs ∧ length xs ≤ length y)
  ∧
  ((o₁ : List (_ × _)) →
   (o₂ : List _) →
   PrefixWitness y xs o₂ o₁ →
   NonEmpty o₂)

NonemptyResultBranch :
  {A : Set} →
  A →
  List (A × A) →
  List A →
  List (A × A) →
  List A →
  Set
NonemptyResultBranch x₀ r ys r₁ [] = ⊥
NonemptyResultBranch x₀ r ys r₁ (x₁ ∷ x₂) =
  r ≡ (x₀ , x₁) ∷ r₁
  ∧ ys ≡ x₂

ResultPremise :
  {A : Set} →
  List A →
  List A →
  List (A × A) →
  List A →
  Set
ResultPremise [] y r ys =
  r ≡ [] ∧ ys ≡ y
ResultPremise (x₀ ∷ xs) y r ys =
  Σ (List (_ × _)) λ r₁ →
  Σ (List _) λ ys₁ →
    PrefixWitness y xs ys₁ r₁
    ∧ NonemptyResultBranch x₀ r ys r₁ ys₁

ResultConclusion :
  {A : Set} →
  List A →
  List A →
  List (A × A) →
  List A →
  Set
ResultConclusion x y r ys =
  Σ (List _) λ y₀ →
    y ≡ y₀ ++ ys
    ∧ length y₀ ≡ length x
    ∧ r ≡ zip x (reverse y₀)

convolution-rec'vc : Set₁
convolution-rec'vc =
  (A : Set) →
  (inhabitedA : Inhabited A) →
  (x y : List A) →
  length x ≤ length y →
  RecursiveCallObligation x y
  ∧
  ((r : List (A × A)) →
   (ys : List A) →
   ResultPremise x y r ys →
   ResultConclusion x y r ys)
