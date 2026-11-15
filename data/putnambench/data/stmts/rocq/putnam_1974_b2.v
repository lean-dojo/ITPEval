(* Statement-only formalization of PutnamBench artifact putnam_1974_b2: asymptotic vanishing of a continuously differentiable real function and its derivative; this file contains no proof. *)
From Stdlib Require Import Reals ClassicalEpsilon.

Open Scope R_scope.

Definition real_derivative (f : R -> R) (x : R) : R :=
  epsilon (inhabits (0 : R)) (fun d : R => derivable_pt_lim f x d).

Definition tends_to_at_pos_infty (f : R -> R) (l : R) : Prop :=
  forall eps : R,
    eps > 0 ->
    exists M : R, forall x : R, x >= M -> Rabs (f x - l) < eps.

Theorem putnam_1974_b2
    (y : R -> R)
    (ycontdiff :
      (forall x : R, derivable_pt_lim y x (real_derivative y x)) /\
      continuity (real_derivative y))
    (limy :
      tends_to_at_pos_infty
        (fun x : R => (real_derivative y x) ^ 2 + (y x) ^ 3)
        0)
    : tends_to_at_pos_infty y 0 /\
      tends_to_at_pos_infty (real_derivative y) 0.
Admitted.
