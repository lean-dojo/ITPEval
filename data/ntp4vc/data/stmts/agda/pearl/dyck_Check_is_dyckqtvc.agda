-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/dyck_Check_is_dyckqtvc: a Dyck-word checking verification condition
-- relating a unique valid prefix decomposition to the returned Boolean, and
-- ruling out Dyck words when no valid prefix exists. This file contains no proof.

{-# OPTIONS --safe #-}

module dyck_Check_is_dyckqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)

infixr 5 _++_
infixr 3 _∧_
infix 2 _↔_

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data Paren : Set where
  L R : Paren

data Dyck : List Paren → Set where
  dyck-nil : Dyck []
  dyck-wrap :
    (w₁ w₂ : List Paren) →
    Dyck w₁ →
    Dyck w₂ →
    Dyck (L ∷ (w₁ ++ (R ∷ w₂)))

TailAllowed : List Paren → Set
TailAllowed (L ∷ _) = ⊥
TailAllowed _ = ⊤

Fall : List Paren → List Paren → Set
Fall p s = Dyck p ∧ TailAllowed s

UniqueSplit :
  List Paren →
  List Paren →
  List Paren →
  Set
UniqueSplit source prefix suffix =
  (p₂ : List Paren) →
  (s : List Paren) →
  (source ≡ p₂ ++ s ∧ Fall p₂ s) →
  (p₂ ≡ prefix ∧ s ≡ suffix)

Split :
  List Paren →
  List Paren →
  List Paren →
  Set
Split source prefix suffix =
  source ≡ prefix ++ suffix ∧
  Fall prefix suffix ∧
  UniqueSplit source prefix suffix

ResultMatches : List Paren → Bool → Set
ResultMatches [] result = result ≡ true
ResultMatches (_ ∷ _) result = result ≡ false

NoFall : List Paren → Set
NoFall source =
  (p : List Paren) →
  (s : List Paren) →
  source ≡ p ++ s →
  Not (Fall p s)

ChosenPrefixCase : List Paren → List Paren → Set
ChosenPrefixCase w o₂ =
  (o₁ : List Paren) →
  Split w o₂ o₁ →
  (result : Bool) →
  ResultMatches o₁ result →
  ((result ≡ true) ↔ Dyck w)

IsDyckCondition : List Paren → List Paren → Set
IsDyckCondition w o₂ =
  ChosenPrefixCase w o₂ ∧
  (NoFall w → Not (Dyck w))

is-dyck'vc : Set
is-dyck'vc =
  (w : List Paren) →
  (o₂ : List Paren) →
  IsDyckCondition w o₂
