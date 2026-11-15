-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/there_and_back_again_Convolution_convolutionqtvc: the symbolic
-- convolution verification condition for equal-length lists, relating a
-- consumed prefix of the second list to zipped reversed output. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module there_and_back_again_Convolution_convolutionqtvc where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)

infix 4 _≤_
infixr 5 _++_
infixr 4 _×_
infixr 3 _∧_

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

PrefixWitness :
  {A : Set} →
  List A →
  List A →
  List A →
  List (A × A) →
  Set
PrefixWitness x y suffix pairs =
  Σ (List _) λ y₀ →
    y ≡ y₀ ++ suffix
    ∧ length y₀ ≡ length x
    ∧ pairs ≡ zip x (reverse y₀)

convolution'vc : Set₁
convolution'vc =
  (A : Set) →
  Inhabited A →
  (x y : List A) →
  length x ≡ length y →
  length x ≤ length y
  ∧
  ((o₁ : List (A × A)) →
   (o₂ : List A) →
   PrefixWitness x y o₂ o₁ →
   o₁ ≡ zip x (reverse y))
