(* Statement-only formalization of Logipedia corpus artifact
   bigops.sym_eq_bigop_S (catalog title "bigops.sym_eq_bigop_S"):
   directed Leibniz equality at a successor index from the polymorphic
   big-operation body to the big-operation function. This file contains no
   proof. *)

Definition leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter bigop bigop_body :
  forall H : Type,
    nat -> (nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H.

Theorem bigops_sym_eq_bigop_S :
  forall (H : Type) (n : nat),
    leibniz
      ((nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H)
      (bigop_body H (S n))
      (bigop H (S n)).
Admitted.
