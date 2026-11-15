-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/defunctionalization_Defunctionalization_eval_2qtvc: the expression
-- evaluator verification condition, combining a branch-specific size
-- decrease with preservation of defunctionalized continuation evaluation.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module defunctionalization_Defunctionalization_eval_2qtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

_≤Z_ : Int → Int → Set
x ≤Z y = intLessOrEqual x y ≡ true

_<Z_ : Int → Int → Set
x <Z y = intLess x y ≡ true

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

eval₀ : Expr → Int
eval₀ (Cte n) = n
eval₀ (Sub e₁ e₂) = subtractInt (eval₀ e₁) (eval₀ e₂)

data Cont : Set where
  A1 : Expr → Cont → Cont
  A2 : Int → Cont → Cont
  I  : Cont

data EvalCont : Cont → Int → Int → Set where
  a1 :
    {v r : Int} →
    {k : Cont} →
    {e₂ : Expr} →
    EvalCont (A2 v k) (eval₀ e₂) r →
    EvalCont (A1 e₂ k) v r
  a2 :
    {v₁ v r : Int} →
    {k : Cont} →
    EvalCont k (subtractInt v₁ v) r →
    EvalCont (A2 v₁ k) v r
  a3 :
    {v : Int} →
    EvalCont I v v

sizeE : Expr → Int
sizeE (Cte _) = oneZ
sizeE (Sub e₁ e₂) =
  addInt (addInt threeZ (sizeE e₁)) (sizeE e₂)

sizeC : Cont → Int
sizeC I = zeroZ
sizeC (A1 e₂ k) =
  addInt (addInt twoZ (sizeE e₂)) (sizeC k)
sizeC (A2 _ k) =
  addInt oneZ (sizeC k)

DecreaseCondition : Expr → Cont → Set
DecreaseCondition e@(Cte _) c =
  zeroZ ≤Z addInt (sizeC c) (sizeE e) ∧
  sizeC c <Z addInt (sizeC c) (sizeE e)
DecreaseCondition e@(Sub e₁ e₂) c =
  zeroZ ≤Z addInt (sizeC c) (sizeE e) ∧
  addInt (sizeC (A1 e₂ c)) (sizeE e₁)
    <Z addInt (sizeC c) (sizeE e)

EvaluationPremise : Expr → Cont → Int → Set
EvaluationPremise (Cte n) c result =
  EvalCont c n result
EvaluationPremise (Sub e₁ e₂) c result =
  EvalCont (A1 e₂ c) (eval₀ e₁) result

eval-2'vc : Set
eval-2'vc =
  (e : Expr) →
  (c : Cont) →
  DecreaseCondition e c ∧
  ((result : Int) →
   EvaluationPremise e c result →
   EvalCont c (eval₀ e) result)
