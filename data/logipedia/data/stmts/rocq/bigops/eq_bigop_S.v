(* Statement-only formalization of Logipedia corpus artifact
   bigops.eq_bigop_S: the Leibniz equality at a successor index between a
   polymorphic big-operation function and its body. This file contains no
   proof. *)

Definition leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter bigop bigop_body :
  forall H : Type,
    nat -> (nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H.

Theorem bigops_eq_bigop_S :
  forall (H : Type) (n : nat),
    leibniz
      ((nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H)
      (bigop H (S n))
      (bigop_body H (S n)).
Admitted.
