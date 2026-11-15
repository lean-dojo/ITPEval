-- Statement-only formalization of Logipedia corpus artifact "div_mod.sym_eq_div_aux"
-- (catalog title "div_mod.sym_eq_div_aux"): at every natural fuel index, the naturally
-- filtered division body is Leibniz-equal to the division auxiliary. This file contains no proof.

namespace div_mod

def Leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

def filterNatType (R : Type) (f : Nat → R) (p : Nat) : R :=
  f p

def divAux : Nat → Nat → Nat → Nat
  | 0, _m, _n => 0
  | Nat.succ p, m, n =>
      if m ≤ n then 0 else Nat.succ (divAux p (m - Nat.succ n) n)

def divAuxBody : Nat → Nat → Nat → Nat
  | 0, _m, _n => 0
  | Nat.succ p, m, n =>
      if m ≤ n then 0 else Nat.succ (divAux p (m - Nat.succ n) n)

theorem sym_eq_div_aux :
    ∀ p : Nat,
      Leibniz (Nat → Nat → Nat)
        (filterNatType (Nat → Nat → Nat) divAuxBody p) (divAux p) := sorry

end div_mod
