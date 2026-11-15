-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/defunctionalization_ReductionSemantics_decompose_termqtvc: the
-- reduction-semantics expression decomposition verification condition,
-- combining expression-and-context size decrease with preservation of
-- recomposition, redex, value, and empty-context properties. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module defunctionalization_ReductionSemantics_decompose_termqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

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

sizeC : Context → Int
sizeC Empty = zeroZ
sizeC (Left c₁ e) =
  addInt (addInt twoZ (sizeC c₁)) (sizeE e)
sizeC (Right _ c₁) =
  addInt oneZ (sizeC c₁)

DecomposeTermCondition : Expr → Context → Set
DecomposeTermCondition e@(Cte n) c =
  (zeroZ ≤Z addInt (sizeE e) (sizeC c) ∧
   sizeC c <Z addInt (sizeE e) (sizeC c)) ∧
  (((c₁ : Context) →
    (e₁ : Expr) →
    (recompose c₁ e₁ ≡ recompose c (Cte n) ∧
     IsARedex e₁) →
    (recompose c₁ e₁ ≡ recompose c e ∧
     IsARedex e₁)) ∧
   (IsEmptyContext c →
    (IsEmptyContext c ∧ IsAValue e)))
DecomposeTermCondition e@(Sub e₁ e₂) c =
  let o₁ = Left c e₂
  in
  (zeroZ ≤Z addInt (sizeE e) (sizeC c) ∧
   addInt (sizeE e₁) (sizeC o₁)
     <Z addInt (sizeE e) (sizeC c)) ∧
  (((c₁ : Context) →
    (e₁₁ : Expr) →
    (recompose c₁ e₁₁ ≡ recompose o₁ e₁ ∧
     IsARedex e₁₁) →
    (recompose c₁ e₁₁ ≡ recompose c e ∧
     IsARedex e₁₁)) ∧
   ((IsEmptyContext o₁ ∧ IsAValue e₁) →
    (IsEmptyContext c ∧ IsAValue e)))

decompose-term'vc : Set
decompose-term'vc =
  (e : Expr) →
  (c : Context) →
  DecomposeTermCondition e c
