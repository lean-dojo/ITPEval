-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/defunctionalization_ReductionSemantics_interpretqtvc: direct
-- evaluation is unchanged when an expression is recomposed with the empty
-- reduction context. This file contains no proof.

{-# OPTIONS --safe #-}

module defunctionalization_ReductionSemantics_interpretqtvc where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

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

interpret'vc : Set
interpret'vc =
  (p : Expr) →
  eval₀ (recompose Empty p) ≡ eval₀ p
