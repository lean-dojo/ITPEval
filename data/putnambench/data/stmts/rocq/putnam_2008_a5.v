(* Statement-only formalization of PutnamBench corpus artifact putnam_2008_a5:
   a degree lower bound for real polynomials whose values at consecutive
   positive integers trace a regular polygon counterclockwise. This file
   contains no proof. *)

From Stdlib Require Import Reals List.

Open Scope R_scope.

Record putnam_2008_a5_polynomial : Type := {
  putnam_2008_a5_coefficients : list R;
  putnam_2008_a5_coefficients_normalized :
    putnam_2008_a5_coefficients = nil \/
    last putnam_2008_a5_coefficients 0 <> 0
}.

Fixpoint putnam_2008_a5_eval_coefficients
    (coefficients : list R) (x : R) : R :=
  match coefficients with
  | nil => 0
  | coefficient :: remaining =>
      coefficient +
      x * putnam_2008_a5_eval_coefficients remaining x
  end.

Definition putnam_2008_a5_eval
    (p : putnam_2008_a5_polynomial) (x : R) : R :=
  putnam_2008_a5_eval_coefficients
    (putnam_2008_a5_coefficients p) x.

Definition putnam_2008_a5_degree
    (p : putnam_2008_a5_polynomial) : nat :=
  Nat.pred (length (putnam_2008_a5_coefficients p)).

Definition putnam_2008_a5_angle (n k : nat) : R :=
  2 * PI * INR k / INR n.

Theorem putnam_2008_a5
    (n : nat)
    (hn : (3 <= n)%nat)
    (f g : putnam_2008_a5_polynomial)
    (hfg :
      exists center_re center_im z_re z_im : R,
        ~ (z_re = 0 /\ z_im = 0) /\
        forall k : nat,
          (1 <= k <= n)%nat ->
          putnam_2008_a5_eval f (INR k) =
            center_re +
              (z_re * cos (putnam_2008_a5_angle n k) -
               z_im * sin (putnam_2008_a5_angle n k)) /\
          putnam_2008_a5_eval g (INR k) =
            center_im +
              (z_re * sin (putnam_2008_a5_angle n k) +
               z_im * cos (putnam_2008_a5_angle n k))) :
  ((n - 1 <= putnam_2008_a5_degree f)%nat \/
   (n - 1 <= putnam_2008_a5_degree g)%nat).
Admitted.
