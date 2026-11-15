-- Statement-only formalization of Logipedia corpus artifact "nat.eq_plus_body_S"
-- (catalog title "nat.eq_plus_body_S"): Leibniz equality relates the recursive
-- addition body at a successor to the successor of addition at the preceding
-- natural number. This file contains no proof.

namespace nat

def Leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

def plus : Nat → Nat → Nat
  | 0, m => m
  | Nat.succ n, m => Nat.succ (plus n m)

def plusBody : Nat → Nat → Nat
  | 0, m => m
  | Nat.succ n, m => Nat.succ (plus n m)

theorem eq_plus_body_S :
    ∀ n : Nat,
      Leibniz (Nat → Nat) (plusBody (Nat.succ n))
        (fun m ↦ Nat.succ (plus n m)) := sorry

end nat
