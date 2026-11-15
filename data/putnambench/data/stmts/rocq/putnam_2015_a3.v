Require Import Reals ROrderedType Coquelicot.Coquelicot. 
Open Scope R_scope.

Fixpoint putnam_2015_a3_prod (f : nat -> C) (n : nat) : C :=
  match n with
  | O => RtoC 1
  | S n' => Cmult (putnam_2015_a3_prod f n') (f (S n'))
  end.

Definition putnam_2015_a3_factor (a b : nat) : C :=
  let theta : R := 2 * PI * INR a * INR b / 2015 in
  (1 + cos theta, sin theta).

Definition putnam_2015_a3_solution : nat := 13725.

(* This product identity is the branch-independent form of the requested
   base-2 logarithm computation. *)
Theorem putnam_2015_a3 :
    putnam_2015_a3_prod
      (fun a =>
        putnam_2015_a3_prod
          (fun b => putnam_2015_a3_factor a b)
          2015)
      2015
    = RtoC (pow 2 putnam_2015_a3_solution).
Proof. Admitted.
