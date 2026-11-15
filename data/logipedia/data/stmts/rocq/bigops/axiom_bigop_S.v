(* Statement-only formalization of Logipedia corpus artifact
   bigops.axiom_bigop_S: the polymorphic connectives.equal relation at a
   successor index between a big-operation function and its body. This file
   contains no proof. *)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.

Parameter bigop bigop_body :
  forall H : Type,
    nat -> (nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H.

Theorem bigops_axiom_bigop_S :
  forall (H : Type) (n : nat),
    connectives_equal
      ((nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H)
      (bigop H (S n))
      (bigop_body H (S n)).
Admitted.
