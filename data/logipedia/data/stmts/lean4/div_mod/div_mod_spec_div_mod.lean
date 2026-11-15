-- Statement-only formalization of Logipedia corpus artifact
-- "div_mod.div_mod_spec_div_mod" (catalog title "div_mod.div_mod_spec_div_mod"):
-- for every positive natural divisor, the source fuel-recursive quotient and
-- remainder satisfy the division-with-remainder specification. This file contains no proof.

namespace div_mod

def modAux : Nat -> Nat -> Nat -> Nat
  | 0, n, _m => n
  | Nat.succ p, n, m =>
      if n <= m then n else modAux p (n - Nat.succ m) m

def divAux : Nat -> Nat -> Nat -> Nat
  | 0, _n, _m => 0
  | Nat.succ p, n, m =>
      if n <= m then 0 else Nat.succ (divAux p (n - Nat.succ m) m)

def mod (n m : Nat) : Nat :=
  match m with
  | 0 => n
  | Nat.succ p => modAux n n p

def div (n m : Nat) : Nat :=
  match m with
  | 0 => Nat.succ n
  | Nat.succ p => divAux n n p

def div_mod_spec (n m q r : Nat) : Prop :=
  r < m /\ n = q * m + r

theorem div_mod_spec_div_mod :
    forall n m : Nat, 0 < m -> div_mod_spec n m (div n m) (mod n m) := sorry

end div_mod
