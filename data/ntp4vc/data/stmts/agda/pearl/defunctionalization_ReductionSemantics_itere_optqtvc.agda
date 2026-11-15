-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/defunctionalization_ReductionSemantics_itere_optqtvc: the
-- reduction-semantics iteration verification condition, preserving redex
-- decomposition and direct evaluation under context recomposition, with the
-- terminal empty-context value result characterized exactly. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module defunctionalization_ReductionSemantics_itere_optqtvc where

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

IsAValue : Expr → Set
IsAValue (Cte _) = ⊤
IsAValue _ = ⊥

IsEmptyContext : Context → Set
IsEmptyContext Empty = ⊤
IsEmptyContext _ = ⊥

ConstantShape : Expr → Set
ConstantShape (Cte _) = ⊤
ConstantShape _ = ⊥

ResultMatchesConstant : Expr → Int → Set
ResultMatchesConstant (Cte n) result = result ≡ n
ResultMatchesConstant _ _ = ⊥

itere-opt'vc : Set
itere-opt'vc =
  (c₁ : Context) →
  (e : Expr) →
  (((c : Context) →
    (r : Expr) →
    (recompose c r ≡ recompose c₁ e ∧ IsARedex r) →
    (IsARedex r ∧
     ((o₁ : Expr) →
      eval₀ o₁ ≡ eval₀ r →
      eval₀ (recompose c o₁) ≡ eval₀ (recompose c₁ e)))) ∧
   ((IsEmptyContext c₁ ∧ IsAValue e) →
    (ConstantShape e ∧
     ((result : Int) →
      ResultMatchesConstant e result →
      result ≡ eval₀ (recompose c₁ e)))))
