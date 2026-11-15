-- Statement-only formalization of Logipedia corpus artifact
-- "nat.eq_times_body_O" (catalog title "nat.eq_times_body_O"): Leibniz equality
-- relates the fixed recursive multiplication body at zero to the constant-zero
-- function on natural numbers. This file contains no proof.

namespace nat

def Leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y

def plus : Nat -> Nat -> Nat
  | 0, m => m
  | Nat.succ n, m => Nat.succ (plus n m)

def times : Nat -> Nat -> Nat
  | 0, _m => 0
  | Nat.succ n, m => plus m (times n m)

def timesBody : Nat -> Nat -> Nat
  | 0, _m => 0
  | Nat.succ n, m => plus m (times n m)

theorem eq_times_body_O :
    Leibniz (Nat -> Nat) (timesBody 0) (fun _m => 0) := sorry

end nat
