module Client where

open import Agda.Builtin.Nat using (Nat; zero)

prior : Nat
prior = zero

open import Level using (levelOfType)
open import Algebra using (idNat)

first : Nat
first = idNat zero
