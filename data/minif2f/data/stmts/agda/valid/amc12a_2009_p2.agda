-- Statement-only formalization of miniF2F valid problem amc12a_2009_p2. This file contains no
-- proof.

module amc12a-2009-p2 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

record Rational : Set where
  constructor fraction
  field
    numerator denominator : Nat

infix 4 _≈_

_≈_ : Rational → Rational → Set
fraction a b ≈ fraction c d = a * d ≡ c * b

add : Rational → Rational → Rational
add (fraction a b) (fraction c d) =
  fraction (a * d + c * b) (b * d)

multiply : Rational → Rational → Rational
multiply (fraction a b) (fraction c d) =
  fraction (a * c) (b * d)

reciprocal : Rational → Rational
reciprocal (fraction a b) = fraction b a

divide : Rational → Rational → Rational
divide x y = multiply x (reciprocal y)

one : Rational
one = fraction 1 1

amc12a-2009-p2 : Set
amc12a-2009-p2 =
  add one
    (divide one
      (add one
        (divide one
          (add one one))))
  ≈ fraction 5 3
