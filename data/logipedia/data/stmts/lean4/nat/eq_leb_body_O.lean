-- Statement-only formalization of Logipedia corpus artifact "nat.eq_leb_body_O"
-- (catalog title "nat.eq_leb_body_O"): Leibniz equality identifies the
-- less-than-or-equal test body at zero with the constant-true Boolean function
-- on natural numbers. This file contains no proof.

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

theorem eq_leb_body_O :
    Leibniz (Nat → Bool) (leb_body 0) (fun _m ↦ true) := sorry

end nat
