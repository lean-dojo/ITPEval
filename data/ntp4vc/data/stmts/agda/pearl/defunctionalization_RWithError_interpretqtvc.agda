-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/defunctionalization_RWithError_interpretqtvc: evaluation with
-- underflow is preserved when an expression is recomposed with the empty
-- evaluation context. This file contains no proof.

{-# OPTIONS --safe #-}

module defunctionalization_RWithError_interpretqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

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

zeroZ oneZ twoZ threeZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))
threeZ = pos (suc (suc (suc zero)))

data Expr : Set where
  Cte : Int → Expr
  Sub : Expr → Expr → Expr

sizeE : Expr → Int
sizeE (Cte _) = oneZ
sizeE (Sub e₁ e₂) =
  addInt (addInt threeZ (sizeE e₁)) (sizeE e₂)

data Value : Set where
  Vnum      : Int → Value
  Underflow : Value

checkedSubtract : Int → Int → Value
checkedSubtract v₁ v₂ with intLessOrEqual v₂ v₁
... | true = Vnum (subtractInt v₁ v₂)
... | false = Underflow

combineSubtraction : Value → Value → Value
combineSubtraction Underflow _ = Underflow
combineSubtraction (Vnum _) Underflow = Underflow
combineSubtraction (Vnum v₁) (Vnum v₂) =
  checkedSubtract v₁ v₂

evalWithError : Expr → Value
evalWithError (Cte n) with intLessOrEqual zeroZ n
... | true = Vnum n
... | false = Underflow
evalWithError (Sub e₁ e₂) =
  combineSubtraction (evalWithError e₁) (evalWithError e₂)

data Context : Set where
  Empty : Context
  Left  : Context → Expr → Context
  Right : Int → Context → Context

sizeC : Context → Int
sizeC Empty = zeroZ
sizeC (Left c₁ e) =
  addInt (addInt twoZ (sizeC c₁)) (sizeE e)
sizeC (Right _ c₁) =
  addInt oneZ (sizeC c₁)

recompose : Context → Expr → Expr
recompose Empty e = e
recompose (Left c₁ e₂) e =
  recompose c₁ (Sub e e₂)
recompose (Right n₁ c₁) e =
  recompose c₁ (Sub (Cte n₁) e)

interpret'vc : Set
interpret'vc =
  (p : Expr) →
  evalWithError (recompose Empty p) ≡ evalWithError p
