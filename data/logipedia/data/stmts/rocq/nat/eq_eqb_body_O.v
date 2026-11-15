(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_eqb_body_O (catalog title "nat.eq_eqb_body_O"): Leibniz equality
  relates the Boolean equality-test body at natural zero to the natural-number
  matcher with true at zero and false at successors. This file contains no
  proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter eqb_body : nat -> nat -> bool.
Parameter match_nat_type :
  forall return_type : Type,
    return_type -> (nat -> return_type) -> nat -> return_type.

Theorem logipedia_nat_eq_eqb_body_O :
  logipedia_leibniz
    (nat -> bool)
    (eqb_body O)
    (fun m : nat =>
       match_nat_type bool true (fun _ : nat => false) m).
Admitted.
