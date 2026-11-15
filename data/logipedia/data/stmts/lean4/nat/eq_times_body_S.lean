-- Statement-only formalization of Logipedia corpus artifact "nat.eq_times_body_S"
-- (catalog title "nat.eq_times_body_S"): Leibniz equality relates the multiplication
-- body at a successor to the function adding its argument to multiplication at the
-- preceding natural number. This file contains no proof.

namespace nat

def Leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y

-- itpeval-source-signature: logipedia:nat.plus as plus
axiom plus : Nat -> Nat -> Nat

-- itpeval-source-signature: logipedia:nat.times as times
axiom times : Nat -> Nat -> Nat

-- itpeval-source-signature: logipedia:nat.times_body as timesBody
axiom timesBody : Nat -> Nat -> Nat

theorem eq_times_body_S :
    forall n : Nat,
      Leibniz (Nat -> Nat) (timesBody (Nat.succ n))
        (fun m => plus m (times n m)) := sorry

end nat
