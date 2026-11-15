-- Statement-only formalization of "Solutions to Pell's Equation" from Hundred Theorems item
-- 039. This file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _≤_ _<_
infixl 6 _+z_
infixl 7 _*z_
infixr 3 _∧_
infix 1 _↔_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

record _∧_ (A B : Set) : Set where
  constructor both
  field
    left-conjunct : A
    right-conjunct : B

record _↔_ (A B : Set) : Set where
  constructor equivalence
  field
    forward : A → B
    backward : B → A

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value : A
    property : P value

record NatPair : Set where
  constructor pair
  field
    x-component : Nat
    y-component : Nat

open NatPair

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

_+z_ : Int → Int → Int
pos m +z pos n = pos (m + n)
pos m +z negsuc n = difference m (suc n)
negsuc m +z pos n = difference n (suc m)
negsuc m +z negsuc n = negsuc (suc (m + n))

_*z_ : Int → Int → Int
pos m *z pos n = pos (m * n)
pos m *z negsuc n = negative (m * suc n)
negsuc m *z pos n = negative (suc m * n)
negsuc m *z negsuc n = pos (suc m * suc n)

absInt : Int → Nat
absInt (pos n) = n
absInt (negsuc n) = suc n

squareNat : Nat → Nat
squareNat n = n * n

squareInt : Int → Int
squareInt z = z *z z

PellSolution : Nat → Int → Int → Set
PellSolution D x y =
  squareInt x ≡ pos 1 +z (pos D *z squareInt y)

NonSquare : Nat → Set
NonSquare D = (k : Nat) → D ≠ squareNat k

pellStep : Nat → Nat → Nat → NatPair → NatPair
pellStep D x0 y0 p =
  pair
    (x-component p * x0 + D * (y-component p * y0))
    (x-component p * y0 + y-component p * x0)

pellPower : Nat → Nat → Nat → Nat → NatPair
pellPower D x0 y0 zero = pair 1 0
pellPower D x0 y0 (suc n) =
  pellStep D x0 y0 (pellPower D x0 y0 n)

AllSolutionsGenerated : Nat → Nat → Nat → Set
AllSolutionsGenerated D x0 y0 =
  (x y : Int) →
  PellSolution D x y ↔
  Exists Nat (λ n →
    (absInt x ≡ x-component (pellPower D x0 y0 n)) ∧
    (absInt y ≡ y-component (pellPower D x0 y0 n)))

AlmostSquareGenerator : Nat → Nat → Nat → Set
AlmostSquareGenerator D x0 y0 =
  (a : Nat) →
  1 < a →
  suc D ≡ squareNat a →
  (x0 ≡ a) ∧ (y0 ≡ 1)

solutions-to-pell-s-equation : Set
solutions-to-pell-s-equation =
  (D : Nat) →
  NonSquare D →
  Exists Nat (λ x0 →
    Exists Nat (λ y0 →
      (y0 ≠ zero) ∧
      (PellSolution D (pos x0) (pos y0) ∧
      (AllSolutionsGenerated D x0 y0 ∧
       AlmostSquareGenerator D x0 y0))))
