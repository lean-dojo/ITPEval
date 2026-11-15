-- Statement-only formalization of miniF2F test problem numbertheory_x5neqy2p4. This file
-- contains no proof.

module numbertheory_x5neqy2p4 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_
infixl 6 _+z_
infixl 7 _*z_
infixr 8 _^z_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

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

_^z_ : Int → Nat → Int
base ^z zero = pos 1
base ^z (suc exponent) = base *z (base ^z exponent)

numbertheory_x5neqy2p4 : Set
numbertheory_x5neqy2p4 =
  (x y : Int) →
  x ^z 5 ≠ (y ^z 2) +z pos 4
