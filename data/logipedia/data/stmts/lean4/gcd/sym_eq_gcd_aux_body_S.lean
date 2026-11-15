-- Statement-only formalization of Logipedia corpus artifact
-- "gcd.sym_eq_gcd_aux_body_S" (catalog title "gcd.sym_eq_gcd_aux_body_S"):
-- at every successor recursion index, the binary natural-number function that
-- returns the second input when it divides the first, and otherwise applies
-- the preceding auxiliary greatest-common-divisor function to that input and
-- their remainder, is Leibniz-equal to the auxiliary body.
-- This file contains no proof.

namespace gcd

def dividesb (n m : Nat) : Bool :=
  m % n == 0

def gcdAux : Nat → Nat → Nat → Nat
  | 0, m, _n => m
  | Nat.succ p, m, n =>
      bif dividesb n m then n else gcdAux p n (m % n)

def gcdAuxBody : Nat → Nat → Nat → Nat
  | 0, m, _n => m
  | Nat.succ p, m, n =>
      bif dividesb n m then n else gcdAux p n (m % n)

theorem sym_eq_gcd_aux_body_S :
    ∀ p : Nat, ∀ P : (Nat → Nat → Nat) → Prop,
      P (fun (m n : Nat) ↦
        bif dividesb n m then n else gcdAux p n (m % n)) →
      P (gcdAuxBody (Nat.succ p)) := sorry

end gcd
