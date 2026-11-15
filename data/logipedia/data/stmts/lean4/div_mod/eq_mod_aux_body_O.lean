-- Statement-only formalization of Logipedia corpus artifact
-- "div_mod.eq_mod_aux_body_O" (catalog title "div_mod.eq_mod_aux_body_O"):
-- Leibniz equality identifies the fixed source modulus auxiliary body at zero
-- with the binary natural-number first projection. This file contains no proof.

namespace div_mod

def Leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y

def modAux : Nat -> Nat -> Nat -> Nat
  | 0, m, _n => m
  | Nat.succ p, m, n =>
      if m <= n then m else modAux p (m - Nat.succ n) n

def modAuxBody : Nat -> Nat -> Nat -> Nat
  | 0, m, _n => m
  | Nat.succ p, m, n =>
      if m <= n then m else modAux p (m - Nat.succ n) n

theorem eq_mod_aux_body_O :
    Leibniz (Nat -> Nat -> Nat) (modAuxBody 0)
      (fun (m _n : Nat) => m) := sorry

end div_mod
