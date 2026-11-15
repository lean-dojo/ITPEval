-- Statement-only formalization of Logipedia corpus artifact
-- "div_mod.eq_div_aux_body_O" (catalog title "div_mod.eq_div_aux_body_O"):
-- Leibniz equality identifies the zero-indexed division auxiliary body with the
-- constant-zero binary natural-number function. This file contains no proof.

namespace div_mod

def Leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y

def divAux : Nat -> Nat -> Nat -> Nat
  | 0, _m, _n => 0
  | Nat.succ p, m, n =>
      if m <= n then 0 else Nat.succ (divAux p (m - Nat.succ n) n)

def divAuxBody : Nat -> Nat -> Nat -> Nat
  | 0, _m, _n => 0
  | Nat.succ p, m, n =>
      if m <= n then 0 else Nat.succ (divAux p (m - Nat.succ n) n)

theorem eq_div_aux_body_O :
    Leibniz (Nat -> Nat -> Nat) (divAuxBody 0)
      (fun (_m _n : Nat) => 0) := sorry

end div_mod
