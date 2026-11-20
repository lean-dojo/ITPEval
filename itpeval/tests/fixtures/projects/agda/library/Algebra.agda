module Algebra where
open import Agda.Builtin.Nat using (Nat; zero)
idNat : Nat → Nat
idNat n = n
test : Nat
test = idNat zero
