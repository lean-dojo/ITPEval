-- Statement-only formalization of Hundred Theorems artifact hundred-theorems__agda__060,
-- "Bézout's Theorem": any two integers admit integer coefficients whose linear combination
-- equals their nonnegative greatest common divisor. This file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infixl 6 _+z_
infixl 7 _*z_

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

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

gcdWithFuel : Nat → Nat → Nat → Nat
gcdWithFuel zero a b = a
gcdWithFuel (suc fuel) a zero = a
gcdWithFuel (suc fuel) a (suc b) =
  gcdWithFuel fuel (suc b) (naturalMod a (suc b))

euclideanGCD : Nat → Nat → Nat
euclideanGCD a b =
  gcdWithFuel (suc (a + b)) a b

bézout-s-theorem : Set
bézout-s-theorem =
  (x y : Int) →
  Exists Int (λ u →
    Exists Int (λ v →
      (u *z x) +z (v *z y) ≡
      pos (euclideanGCD (absInt x) (absInt y))))
