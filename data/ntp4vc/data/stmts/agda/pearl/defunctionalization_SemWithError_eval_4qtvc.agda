-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/defunctionalization_SemWithError_eval_4qtvc: the error-aware
-- defunctionalized evaluator verification condition, combining
-- expression-size decrease with preservation of continuation evaluation.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module defunctionalization_SemWithError_eval_4qtvc where

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

data Cont : Set where
  I : Cont
  A : Expr → Cont → Cont
  B : Int → Cont → Cont

data EvalCont : Cont → Value → Value → Set where
  underflow :
    {k : Cont} →
    EvalCont k Underflow Underflow
  a1 :
    {v : Int} →
    {k : Cont} →
    {e₂ : Expr} →
    {r : Value} →
    EvalCont (B v k) (evalWithError e₂) r →
    EvalCont (A e₂ k) (Vnum v) r
  a2 :
    {k : Cont} →
    {v v₁ : Int} →
    {r : Value} →
    EvalCont k (checkedSubtract v₁ v) r →
    EvalCont (B v₁ k) (Vnum v) r
  a3 :
    {v : Int} →
    EvalCont I (Vnum v) (Vnum v)

sizeC : Cont → Int
sizeC I = zeroZ
sizeC (A e₂ k) =
  addInt (addInt twoZ (sizeE e₂)) (sizeC k)
sizeC (B _ k) =
  addInt oneZ (sizeC k)

DecreaseCondition : Expr → Cont → Set
DecreaseCondition e@(Cte n) c =
  zeroZ ≤Z n →
  ((zeroZ ≤Z addInt (sizeC c) (sizeE e) ∧
    sizeC c <Z addInt (sizeC c) (sizeE e)) ∧
   zeroZ ≤Z n)
DecreaseCondition e@(Sub e₁ e₂) c =
  zeroZ ≤Z addInt (sizeC c) (sizeE e) ∧
  addInt (sizeC (A e₂ c)) (sizeE e₁)
    <Z addInt (sizeC c) (sizeE e)

EvaluationPremise : Expr → Cont → Value → Set
EvaluationPremise (Cte n) c result
  with intLessOrEqual zeroZ n
... | true =
  EvalCont c (Vnum n) result
... | false =
  result ≡ Underflow
EvaluationPremise (Sub e₁ e₂) c result =
  EvalCont (A e₂ c) (evalWithError e₁) result

eval-4'vc : Set
eval-4'vc =
  (e : Expr) →
  (c : Cont) →
  DecreaseCondition e c ∧
  ((result : Value) →
   EvaluationPremise e c result →
   EvalCont c (evalWithError e) result)
