-- Statement-only formalization of "Formula for Pythagorean Triples" from Hundred Theorems item
-- 023. This file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixl 6 _+z_ _-z_
infixl 7 _*z_
infixr 3 _∧_
infixr 2 _∨_
infix 1 _↔_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data _∨_ (A B : Set) : Set where
  or-left : A → A ∨ B
  or-right : B → A ∨ B

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

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

negateInt : Int → Int
negateInt (pos n) = negative n
negateInt (negsuc n) = pos (suc n)

_+z_ : Int → Int → Int
pos m +z pos n = pos (m + n)
pos m +z negsuc n = difference m (suc n)
negsuc m +z pos n = difference n (suc m)
negsuc m +z negsuc n = negsuc (suc (m + n))

_-z_ : Int → Int → Int
x -z y = x +z negateInt y

_*z_ : Int → Int → Int
pos m *z pos n = pos (m * n)
pos m *z negsuc n = negative (m * suc n)
negsuc m *z pos n = negative (suc m * n)
negsuc m *z negsuc n = pos (suc m * suc n)

square : Int → Int
square x = x *z x

PythagoreanTriple : Int → Int → Int → Set
PythagoreanTriple x y z =
  square x +z square y ≡ square z

oddLeg : Int → Int → Int → Int
oddLeg k m n = k *z (square m -z square n)

evenLeg : Int → Int → Int → Int
evenLeg k m n = k *z ((pos 2 *z m) *z n)

hypotenuse : Int → Int → Int → Int
hypotenuse k m n = k *z (square m +z square n)

ParameterizedTriple : Int → Int → Int → Int → Int → Int → Set
ParameterizedTriple x y z k m n =
  (((x ≡ oddLeg k m n) ∧ (y ≡ evenLeg k m n)) ∨
   ((x ≡ evenLeg k m n) ∧ (y ≡ oddLeg k m n))) ∧
  ((z ≡ hypotenuse k m n) ∨
   (z ≡ hypotenuse (negateInt k) m n))

formula-for-pythagorean-triples : Set
formula-for-pythagorean-triples =
  (x y z : Int) →
  PythagoreanTriple x y z ↔
  Exists Int (λ k →
    Exists Int (λ m →
      Exists Int (λ n →
        ParameterizedTriple x y z k m n)))
