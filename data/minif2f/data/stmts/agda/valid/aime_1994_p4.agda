-- Statement-only formalization of miniF2F valid problem aime_1994_p4. This file contains no
-- proof.

module aime-1994-p4 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _<_; div-helper)

NatLess : Nat → Nat → Set
NatLess m n = (m < n) ≡ true

naturalDiv : Nat → Nat → Nat
naturalDiv numerator zero = zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

floorLog₂Aux : Nat → Nat → Nat
floorLog₂Aux zero n = zero
floorLog₂Aux (suc fuel) zero = zero
floorLog₂Aux (suc fuel) (suc zero) = zero
floorLog₂Aux (suc fuel) (suc (suc n)) =
  suc (floorLog₂Aux fuel (naturalDiv (suc (suc n)) 2))

floorLog₂ : Nat → Nat
floorLog₂ n = floorLog₂Aux n n

sumFloorLogs : Nat → Nat
sumFloorLogs zero = zero
sumFloorLogs (suc n) =
  sumFloorLogs n + floorLog₂ (suc n)

aime-1994-p4 : Set
aime-1994-p4 =
  (n : Nat) →
  NatLess zero n →
  sumFloorLogs n ≡ 1994 →
  n ≡ 312
