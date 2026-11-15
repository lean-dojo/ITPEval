-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/defunctionalization_RWithError_eval_1qtvc: the error-aware evaluator
-- verification condition, combining branch-specific size decrease with
-- preservation of evaluation under expression-context recomposition.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module defunctionalization_RWithError_eval_1qtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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

measure : Context → Expr → Int
measure c e =
  multiplyInt twoZ (addInt (sizeC c) (sizeE e))

BranchCondition : Expr → Context → Set
BranchCondition e@(Cte n) c =
  zeroZ ≤Z n →
  ((zeroZ ≤Z measure c e ∧
    addInt oneZ (multiplyInt twoZ (sizeC c)) <Z measure c e) ∧
   zeroZ ≤Z n)
BranchCondition e@(Sub e₁ e₂) c =
  zeroZ ≤Z measure c e ∧
  multiplyInt
    twoZ
    (addInt (sizeC (Left c e₂)) (sizeE e₁))
    <Z measure c e

EvaluationPremise : Expr → Context → Value → Set
EvaluationPremise (Cte n) c result with intLessOrEqual zeroZ n
... | true =
  result ≡ evalWithError (recompose c (Cte n))
... | false =
  result ≡ Underflow
EvaluationPremise (Sub e₁ e₂) c result =
  result ≡ evalWithError (recompose (Left c e₂) e₁)

eval-1'vc : Set
eval-1'vc =
  (e : Expr) →
  (c : Context) →
  BranchCondition e c ∧
  ((result : Value) →
   EvaluationPremise e c result →
   result ≡ evalWithError (recompose c e))
