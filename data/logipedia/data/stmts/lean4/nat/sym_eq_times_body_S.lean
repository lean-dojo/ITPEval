-- Statement-only formalization of Logipedia corpus artifact
-- "nat.sym_eq_times_body_S" (catalog title "nat.sym_eq_times_body_S"):
-- Leibniz equality relates the function adding its argument to multiplication
-- at a natural number to the multiplication body at its successor.
-- This file contains no proof.

namespace nat

def Leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y

-- itpeval-source-signature: logipedia:nat.plus as plus
axiom plus : Nat -> Nat -> Nat

-- itpeval-source-signature: logipedia:nat.times as times
axiom times : Nat -> Nat -> Nat

-- itpeval-source-signature: logipedia:nat.times_body as timesBody
axiom timesBody : Nat -> Nat -> Nat

theorem sym_eq_times_body_S :
    forall n : Nat,
      Leibniz (Nat -> Nat) (fun m => plus m (times n m))
        (timesBody (Nat.succ n)) := sorry

end nat
