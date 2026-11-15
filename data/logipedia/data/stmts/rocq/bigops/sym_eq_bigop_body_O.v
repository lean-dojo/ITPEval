(* Statement-only formalization of Logipedia corpus artifact
   bigops.sym_eq_bigop_body_O (catalog title "bigops.sym_eq_bigop_body_O"):
   directed Leibniz equality identifies the function returning its supplied
   nil element with the zero-index big-operation body. This file contains no
   proof. *)

Definition leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter bigop_body :
  forall H : Type,
    nat -> (nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H.

Theorem bigops_sym_eq_bigop_body_O :
  forall H : Type,
    leibniz
      ((nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H)
      (fun (_p : nat -> bool) (nil : H)
           (_op : H -> H -> H) (_f : nat -> H) => nil)
      (bigop_body H 0).
Admitted.
