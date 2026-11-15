-- Statement-only formalization of Logipedia corpus artifact
-- "div_mod.sym_eq_mod_aux_body_S" (catalog title "div_mod.sym_eq_mod_aux_body_S"):
-- Leibniz equality identifies the Boolean-controlled recursive remainder step with
-- the concrete successor-indexed modulus auxiliary body. This file contains no proof.

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

theorem sym_eq_mod_aux_body_S :
    forall p : Nat,
      Leibniz (Nat -> Nat -> Nat)
        (fun (m n : Nat) =>
          if m <= n then m
          else modAux p (m - Nat.succ n) n)
        (modAuxBody (Nat.succ p)) := sorry

end div_mod
