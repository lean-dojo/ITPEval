-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/dyck_Check_is_dyck_recqtvc: the recursive Dyck-word checking
-- verification condition, including length decrease and unique valid
-- prefix/suffix decomposition obligations. This file contains no proof.

{-# OPTIONS --safe #-}

module dyck_Check_is_dyck_recqtvc where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_)

infixr 5 _++_
infix 4 _≤N_ _<N_
infixr 3 _∧_

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

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

data _≤N_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤N n
  suc≤suc : {m n : Nat} → m ≤N n → suc m ≤N suc n

_<N_ : Nat → Nat → Set
m <N n = suc m ≤N n

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

NoFall : List Paren → Set
NoFall source =
  (p : List Paren) →
  (s : List Paren) →
  source ≡ p ++ s →
  Not (Fall p s)

LengthDecrease : List Paren → List Paren → Set
LengthDecrease whole smaller =
  zero ≤N length whole ∧
  length smaller <N length whole

ResultSplit :
  List Paren →
  List Paren →
  List Paren →
  List Paren →
  Set
ResultSplit w p₀ p₁ w₂ =
  let prefix = L ∷ (p₀ ++ (R ∷ p₁))
  in
  w ≡ prefix ++ w₂ ∧
  Fall prefix w₂ ∧
  UniqueSplit w prefix w₂

SecondStage :
  List Paren →
  List Paren →
  List Paren →
  Set
SecondStage w p₀ [] =
  NoFall w
SecondStage w p₀ (_ ∷ w₁) =
  LengthDecrease w w₁ ∧
  ((p₁ : List Paren) →
   (w₂ : List Paren) →
   Split w₁ p₁ w₂ →
   ResultSplit w p₀ p₁ w₂) ∧
  (NoFall w₁ → NoFall w)

FirstStage :
  List Paren →
  List Paren →
  List Paren →
  Set
FirstStage w w₀ p₀ =
  ((o₁ : List Paren) →
   Split w₀ p₀ o₁ →
   SecondStage w p₀ o₁) ∧
  (NoFall w₀ → NoFall w)

BaseCase : List Paren → Set
BaseCase w =
  w ≡ [] ++ w ∧
  Fall [] w ∧
  UniqueSplit w [] w

IsDyckRecCondition : List Paren → Set
IsDyckRecCondition [] =
  BaseCase []
IsDyckRecCondition (L ∷ w₀) =
  LengthDecrease (L ∷ w₀) w₀ ∧
  ((p₀ : List Paren) →
   FirstStage (L ∷ w₀) w₀ p₀)
IsDyckRecCondition (R ∷ w₀) =
  BaseCase (R ∷ w₀)

is-dyck-rec'vc : Set
is-dyck-rec'vc =
  (w : List Paren) →
  IsDyckRecCondition w
