-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/defunctionalization_ReductionSemantics_reduceqtvc: replacing a redex
-- inside a reduction context by any expression with the same direct integer
-- evaluation preserves the evaluation of the recomposed expression. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module defunctionalization_ReductionSemantics_reduceqtvc where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infixr 3 _∧_

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

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

data Expr : Set where
  Cte : Int → Expr
  Sub : Expr → Expr → Expr

eval₀ : Expr → Int
eval₀ (Cte n) = n
eval₀ (Sub e₁ e₂) = subtractInt (eval₀ e₁) (eval₀ e₂)

IsARedex : Expr → Set
IsARedex (Sub (Cte _) (Cte _)) = ⊤
IsARedex _ = ⊥

data Context : Set where
  Empty : Context
  Left  : Context → Expr → Context
  Right : Int → Context → Context

recompose : Context → Expr → Expr
recompose Empty e = e
recompose (Left c₁ e₂) e =
  recompose c₁ (Sub e e₂)
recompose (Right n₁ c₁) e =
  recompose c₁ (Sub (Cte n₁) e)

reduce'vc : Set
reduce'vc =
  (c : Context) →
  (r : Expr) →
  (e : Expr) →
  (fact₀ : recompose c r ≡ e) →
  (fact₁ : IsARedex r) →
  IsARedex r ∧
  ((result : Expr) →
   Exists Expr
     (λ o₁ →
       eval₀ o₁ ≡ eval₀ r ∧
       result ≡ recompose c o₁) →
   eval₀ result ≡ eval₀ e)
