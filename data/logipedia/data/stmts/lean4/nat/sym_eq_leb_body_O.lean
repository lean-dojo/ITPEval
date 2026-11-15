-- Statement-only formalization of Logipedia corpus artifact "nat.sym_eq_leb_body_O"
-- (catalog title "nat.sym_eq_leb_body_O"): Leibniz equality relates the
-- constant-true Boolean function on natural numbers to the zero case of the
-- fixed recursive less-than-or-equal test body. This file contains no proof.

namespace nat

def Leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

def leb : Nat → Nat → Bool
  | 0, _m => true
  | Nat.succ _n, 0 => false
  | Nat.succ n, Nat.succ m => leb n m

def leb_body : Nat → Nat → Bool
  | 0, _m => true
  | Nat.succ _n, 0 => false
  | Nat.succ n, Nat.succ m => leb n m

theorem sym_eq_leb_body_O :
    Leibniz (Nat → Bool) (fun _m ↦ true) (leb_body 0) := sorry

end nat
