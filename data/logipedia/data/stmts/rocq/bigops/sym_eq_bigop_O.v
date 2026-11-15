(* Statement-only formalization of Logipedia corpus artifact
   bigops.sym_eq_bigop_O: the directed Leibniz equality at zero from the
   polymorphic big-operation body to the big-operation function. This file
   contains no proof. *)

Definition leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter bigop bigop_body :
  forall H : Type,
    nat -> (nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H.

Theorem bigops_sym_eq_bigop_O :
  forall H : Type,
    leibniz
      ((nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H)
      (bigop_body H 0)
      (bigop H 0).
Admitted.
