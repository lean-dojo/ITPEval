-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_668:
-- in integers modulo 7, the inverse of 2 + 3 minus the sum of the inverses
-- of 2 and 3 equals 1. This file contains no proof.

module mathd-numbertheory-668 where

open import Agda.Builtin.Equality using (_≡_)

data ZMod7 : Set where
  zero7 one7 two7 three7 four7 five7 six7 : ZMod7

successor7 : ZMod7 → ZMod7
successor7 zero7 = one7
successor7 one7 = two7
successor7 two7 = three7
successor7 three7 = four7
successor7 four7 = five7
successor7 five7 = six7
successor7 six7 = zero7

add7 : ZMod7 → ZMod7 → ZMod7
add7 x zero7 = x
add7 x one7 = successor7 x
add7 x two7 = successor7 (successor7 x)
add7 x three7 = successor7 (successor7 (successor7 x))
add7 x four7 = successor7 (successor7 (successor7 (successor7 x)))
add7 x five7 =
  successor7 (successor7 (successor7 (successor7 (successor7 x))))
add7 x six7 =
  successor7
    (successor7 (successor7 (successor7 (successor7 (successor7 x)))))

negate7 : ZMod7 → ZMod7
negate7 zero7 = zero7
negate7 one7 = six7
negate7 two7 = five7
negate7 three7 = four7
negate7 four7 = three7
negate7 five7 = two7
negate7 six7 = one7

subtract7 : ZMod7 → ZMod7 → ZMod7
subtract7 x y = add7 x (negate7 y)

inverse7 : ZMod7 → ZMod7
inverse7 zero7 = zero7
inverse7 one7 = one7
inverse7 two7 = four7
inverse7 three7 = five7
inverse7 four7 = two7
inverse7 five7 = three7
inverse7 six7 = six7

mathd-numbertheory-668 : Set
mathd-numbertheory-668 =
  (l r : ZMod7) →
  l ≡ inverse7 (add7 two7 three7) →
  r ≡ add7 (inverse7 two7) (inverse7 three7) →
  subtract7 l r ≡ one7
