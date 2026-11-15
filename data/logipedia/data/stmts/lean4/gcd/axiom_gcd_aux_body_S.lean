-- Statement-only formalization of Logipedia corpus artifact
-- "gcd.axiom_gcd_aux_body_S" (catalog title "gcd.axiom_gcd_aux_body_S"):
-- at every successor recursion index, the concrete auxiliary
-- greatest-common-divisor body unfolds to its divisibility test and preceding
-- fuel-recursive call. This file contains no proof.

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

theorem axiom_gcd_aux_body_S :
    ∀ p : Nat,
      gcdAuxBody (Nat.succ p) =
        fun (m n : Nat) ↦
          bif dividesb n m then n else gcdAux p n (m % n) := sorry

end gcd
