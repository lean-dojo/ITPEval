(* Introducing the assumption exposes a premise for the local implication. *)
Theorem follows_after_intro (p q : Prop) (hpq : p -> q) : p -> q.
Proof.
  intro hp.
  exact (hpq hp).
Qed.
