(* Statement-only formalization of PutnamBench artifact putnam_1982_a4:
   uniqueness of the global continuously differentiable solution of
   y' = -z^3 and z' = y^3 implies a common positive period; this file
   contains no proof. *)

From Stdlib Require Import Reals ClassicalEpsilon.

Open Scope R_scope.

Definition putnam_1982_a4_derivative
    (u : R -> R) (x : R) : R :=
  epsilon (inhabits (0 : R))
    (fun d : R => derivable_pt_lim u x d).

Definition putnam_1982_a4_continuously_differentiable
    (u : R -> R) : Prop :=
  (forall x : R,
      derivable_pt_lim u x (putnam_1982_a4_derivative u x)) /\
  continuity (putnam_1982_a4_derivative u).

Definition putnam_1982_a4_differential_system
    (y z : R -> R) : Prop :=
  y 0 = 1 /\
  z 0 = 0 /\
  putnam_1982_a4_continuously_differentiable y /\
  putnam_1982_a4_continuously_differentiable z /\
  forall x : R,
    putnam_1982_a4_derivative y x = - ((z x) ^ 3) /\
    putnam_1982_a4_derivative z x = (y x) ^ 3.

Definition putnam_1982_a4_pointwise_distinct
    (u v : R -> R) : Prop :=
  ~ forall x : R, u x = v x.

Theorem putnam_1982_a4
    (f g : R -> R)
    (hfgsat : putnam_1982_a4_differential_system f g)
    (hfgonly :
      ~ exists f' g' : R -> R,
          (putnam_1982_a4_pointwise_distinct f f' \/
           putnam_1982_a4_pointwise_distinct g g') /\
          putnam_1982_a4_differential_system f' g') :
  exists L : R,
    L > 0 /\
    forall x : R,
      f (x + L) = f x /\
      g (x + L) = g x.
Admitted.
