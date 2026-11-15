-- Statement-only formalization of Logipedia corpus artifact
-- "div_mod.eq_mod_aux_body_S" (catalog title "div_mod.eq_mod_aux_body_S"):
-- Leibniz equality identifies each fixed successor-indexed modulus auxiliary body with
-- its Boolean-controlled recursive remainder step. This file contains no proof.

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

theorem eq_mod_aux_body_S :
    forall p : Nat,
      Leibniz (Nat -> Nat -> Nat) (modAuxBody (Nat.succ p))
        (fun (m n : Nat) =>
          if m <= n then m
          else modAux p (m - Nat.succ n) n) := sorry

end div_mod
