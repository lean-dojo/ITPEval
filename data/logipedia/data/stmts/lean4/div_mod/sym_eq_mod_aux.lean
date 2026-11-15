-- Statement-only formalization of Logipedia corpus artifact "div_mod.sym_eq_mod_aux"
-- (catalog title "div_mod.sym_eq_mod_aux"): at every natural fuel index, the naturally
-- filtered modulus body is Leibniz-equal to the modulus auxiliary. This file contains no proof.

namespace div_mod

def Leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y

def filterNatType (R : Type) (f : Nat -> R) (p : Nat) : R :=
  f p

def modAux : Nat -> Nat -> Nat -> Nat
  | 0, m, _n => m
  | Nat.succ p, m, n =>
      if m <= n then m else modAux p (m - Nat.succ n) n

def modAuxBody : Nat -> Nat -> Nat -> Nat
  | 0, m, _n => m
  | Nat.succ p, m, n =>
      if m <= n then m else modAux p (m - Nat.succ n) n

theorem sym_eq_mod_aux :
    forall p : Nat,
      Leibniz (Nat -> Nat -> Nat)
        (filterNatType (Nat -> Nat -> Nat) modAuxBody p) (modAux p) := sorry

end div_mod
