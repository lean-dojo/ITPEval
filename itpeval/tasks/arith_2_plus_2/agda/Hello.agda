module Hello where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero + n = n
suc m + n = suc (m + n)

data _≡_ {A : Set} (x : A) : A -> Set where
  refl : x ≡ x

two : Nat
two = suc (suc zero)

four : Nat
four = suc (suc (suc (suc zero)))

two-plus-two : (two + two) ≡ four
two-plus-two = refl
