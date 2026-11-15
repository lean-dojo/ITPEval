-- Statement-only formalization of Logipedia corpus artifact "nat.sym_eq_plus_body_S"
-- (catalog title "nat.sym_eq_plus_body_S"): Leibniz equality relates the
-- successor of addition at a natural number to the recursive addition body at
-- that number's successor. This file contains no proof.

namespace nat

def Leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

def plus : Nat → Nat → Nat
  | 0, m => m
  | Nat.succ n, m => Nat.succ (plus n m)

def plusBody : Nat → Nat → Nat
  | 0, m => m
  | Nat.succ n, m => Nat.succ (plus n m)

theorem sym_eq_plus_body_S :
    ∀ n : Nat,
      Leibniz (Nat → Nat)
        (fun m ↦ Nat.succ (plus n m))
        (plusBody (Nat.succ n)) := sorry

end nat
