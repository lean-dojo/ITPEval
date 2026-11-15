(* Statement-only formalization of Logipedia corpus artifact
   bigops.eq_bigop_body_O (catalog title "bigops.eq_bigop_body_O"):
   Leibniz equality identifies the zero-index big-operation body with the
   function returning its supplied nil element. This file contains no proof. *)

Definition leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter bigop_body :
  forall H : Type,
    nat -> (nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H.

Theorem bigops_eq_bigop_body_O :
  forall H : Type,
    leibniz
      ((nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H)
      (bigop_body H 0)
      (fun (_p : nat -> bool) (nil : H)
           (_op : H -> H -> H) (_f : nat -> H) => nil).
Admitted.
