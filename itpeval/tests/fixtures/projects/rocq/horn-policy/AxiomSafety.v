(* The two targets use the same axiom through different proof contexts. *)
Axiom oracle : forall p : Prop, p.

Theorem global_only (p : Prop) : p.
Proof.
  exact (oracle p).
Qed.

Theorem through_local (p : Prop) : p.
Proof.
  assert (hOracle : p) by exact (oracle p).
  exact hOracle.
Qed.
