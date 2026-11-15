-- Statement-only formalization of miniF2F test problem amc12a_2021_p9. This file contains no
-- proof.

module amc12a-2021-p9 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 8 _^_

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ suc exponent = base * (base ^ exponent)

monus : Nat → Nat → Nat
monus n zero = n
monus zero (suc n) = zero
monus (suc m) (suc n) = monus m n

factor : Nat → Nat
factor k = (2 ^ (2 ^ k)) + (3 ^ (2 ^ k))

finiteProduct : Nat → Nat
finiteProduct zero = 1
finiteProduct (suc n) = finiteProduct n * factor n

amc12a-2021-p9 : Set
amc12a-2021-p9 =
  finiteProduct 7 ≡ monus (3 ^ 128) (2 ^ 128)
