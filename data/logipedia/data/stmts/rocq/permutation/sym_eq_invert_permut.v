(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.sym_eq_invert_permut (catalog title
  "permutation.sym_eq_invert_permut"): for every natural index, the
  natural-type filtered inverse-permutation body is Leibniz-equal to the
  inverse-permutation function. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameter invert_permut invert_permut_body :
  nat -> (nat -> nat) -> nat -> nat.

Theorem permutation_sym_eq_invert_permut :
  forall n : nat,
    logipedia_leibniz
      ((nat -> nat) -> nat -> nat)
      (filter_nat_type
        ((nat -> nat) -> nat -> nat)
        invert_permut_body
        n)
      (invert_permut n).
Admitted.
