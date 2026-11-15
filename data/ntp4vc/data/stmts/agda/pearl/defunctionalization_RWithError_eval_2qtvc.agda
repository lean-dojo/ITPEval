-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/defunctionalization_RWithError_eval_2qtvc: the error-aware evaluator
-- verification condition for a nonnegative constant in an evaluation context,
-- combining branch-specific size decrease with correctness after recomposition.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module defunctionalization_RWithError_eval_2qtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

data ⊤ : Set where
  tt : ⊤

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

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) = negative (m * suc n)
multiplyInt (negsuc m) (pos n) = negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) = pos (suc m * suc n)

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

nextMeasure : Context → Int
nextMeasure c =
  addInt oneZ (multiplyInt twoZ (sizeC c))

BranchCondition : Int → Context → Set
BranchCondition n Empty = ⊤
BranchCondition n c@(Left c₁ e) =
  zeroZ ≤Z nextMeasure c ∧
  multiplyInt
    twoZ
    (addInt (sizeC (Right n c₁)) (sizeE e))
    <Z nextMeasure c
BranchCondition n c@(Right n₁ c₁) =
  n ≤Z n₁ →
  (zeroZ ≤Z nextMeasure c ∧
   multiplyInt
     twoZ
     (addInt (sizeC c₁) (sizeE (Cte (subtractInt n₁ n))))
     <Z nextMeasure c)

EvaluationPremise : Int → Context → Value → Set
EvaluationPremise n Empty result =
  result ≡ Vnum n
EvaluationPremise n (Left c₁ e) result =
  result ≡ evalWithError (recompose (Right n c₁) e)
EvaluationPremise n (Right n₁ c₁) result
  with intLessOrEqual n n₁
... | true =
  result ≡ evalWithError (recompose c₁ (Cte (subtractInt n₁ n)))
... | false =
  result ≡ Underflow

eval-2'vc : Set
eval-2'vc =
  (n : Int) →
  (c : Context) →
  zeroZ ≤Z n →
  BranchCondition n c ∧
  ((result : Value) →
   EvaluationPremise n c result →
   result ≡ evalWithError (recompose c (Cte n)))
