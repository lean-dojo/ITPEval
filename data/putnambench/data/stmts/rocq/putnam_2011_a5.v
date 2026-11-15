(* Statement-only formalization of PutnamBench corpus artifact putnam_2011_a5:
   a bound for pairwise values of a twice continuously differentiable
   real function whose gradient is governed by a positive function satisfying
   x^2 * g(x) <= 1; this file contains no proof. *)

From Stdlib Require Import Vectors.Fin Reals ClassicalEpsilon.

Open Scope R_scope.

Definition putnam_2011_a5_continuous1 (h : R -> R) : Prop :=
  forall x epsilon : R,
    epsilon > 0 ->
    exists delta : R,
      delta > 0 /\
      forall y : R,
        Rabs (y - x) < delta ->
        Rabs (h y - h x) < epsilon.

Definition putnam_2011_a5_distance2
    (x1 x2 y1 y2 : R) : R :=
  sqrt ((x1 - y1) ^ 2 + (x2 - y2) ^ 2).

Definition putnam_2011_a5_continuous2
    (h : R -> R -> R) : Prop :=
  forall x y epsilon : R,
    epsilon > 0 ->
    exists delta : R,
      delta > 0 /\
      forall x' y' : R,
        putnam_2011_a5_distance2 x' y' x y < delta ->
        Rabs (h x' y' - h x y) < epsilon.

Definition putnam_2011_a5_derivable_at
    (h : R -> R) (x d : R) : Prop :=
  forall epsilon : R,
    epsilon > 0 ->
    exists delta : R,
      delta > 0 /\
      forall y : R,
        y <> x ->
        Rabs (y - x) < delta ->
        Rabs ((h y - h x) / (y - x) - d) < epsilon.

Definition putnam_2011_a5_derivative
    (h : R -> R) (x : R) : R :=
  epsilon (inhabits (0 : R))
    (fun d : R => putnam_2011_a5_derivable_at h x d).

Definition putnam_2011_a5_dx
    (F : R -> R -> R) (u v : R) : R :=
  putnam_2011_a5_derivative (fun x : R => F x v) u.

Definition putnam_2011_a5_dy
    (F : R -> R -> R) (u v : R) : R :=
  putnam_2011_a5_derivative (fun y : R => F u y) v.

Definition putnam_2011_a5_dxx
    (F : R -> R -> R) (u v : R) : R :=
  putnam_2011_a5_derivative
    (fun x : R => putnam_2011_a5_dx F x v) u.

Definition putnam_2011_a5_dxy
    (F : R -> R -> R) (u v : R) : R :=
  putnam_2011_a5_derivative
    (fun y : R => putnam_2011_a5_dx F u y) v.

Definition putnam_2011_a5_dyx
    (F : R -> R -> R) (u v : R) : R :=
  putnam_2011_a5_derivative
    (fun x : R => putnam_2011_a5_dy F x v) u.

Definition putnam_2011_a5_dyy
    (F : R -> R -> R) (u v : R) : R :=
  putnam_2011_a5_derivative
    (fun y : R => putnam_2011_a5_dy F u y) v.

Definition putnam_2011_a5_c2_univariate (h : R -> R) : Prop :=
  (forall x : R,
      putnam_2011_a5_derivable_at
        h x (putnam_2011_a5_derivative h x)) /\
  (forall x : R,
      putnam_2011_a5_derivable_at
        (putnam_2011_a5_derivative h) x
        (putnam_2011_a5_derivative
          (putnam_2011_a5_derivative h) x)) /\
  putnam_2011_a5_continuous1 h /\
  putnam_2011_a5_continuous1
    (putnam_2011_a5_derivative h) /\
  putnam_2011_a5_continuous1
    (putnam_2011_a5_derivative
      (putnam_2011_a5_derivative h)).

Definition putnam_2011_a5_c2_bivariate
    (F : R -> R -> R) : Prop :=
  putnam_2011_a5_continuous2 F /\
  (forall u v : R,
      putnam_2011_a5_derivable_at
        (fun x : R => F x v) u (putnam_2011_a5_dx F u v) /\
      putnam_2011_a5_derivable_at
        (fun y : R => F u y) v (putnam_2011_a5_dy F u v)) /\
  putnam_2011_a5_continuous2 (putnam_2011_a5_dx F) /\
  putnam_2011_a5_continuous2 (putnam_2011_a5_dy F) /\
  (forall u v : R,
      putnam_2011_a5_derivable_at
        (fun x : R => putnam_2011_a5_dx F x v)
        u (putnam_2011_a5_dxx F u v) /\
      putnam_2011_a5_derivable_at
        (fun y : R => putnam_2011_a5_dx F u y)
        v (putnam_2011_a5_dxy F u v) /\
      putnam_2011_a5_derivable_at
        (fun x : R => putnam_2011_a5_dy F x v)
        u (putnam_2011_a5_dyx F u v) /\
      putnam_2011_a5_derivable_at
        (fun y : R => putnam_2011_a5_dy F u y)
        v (putnam_2011_a5_dyy F u v)) /\
  putnam_2011_a5_continuous2 (putnam_2011_a5_dxx F) /\
  putnam_2011_a5_continuous2 (putnam_2011_a5_dxy F) /\
  putnam_2011_a5_continuous2 (putnam_2011_a5_dyx F) /\
  putnam_2011_a5_continuous2 (putnam_2011_a5_dyy F).

Definition putnam_2011_a5_gradient_condition
    (F : R -> R -> R) (g : R -> R) : Prop :=
  forall u v : R,
    (putnam_2011_a5_dx F u v = 0 /\
     putnam_2011_a5_dy F u v = 0) \/
    exists c : R,
      putnam_2011_a5_dx F u v = c * g u /\
      putnam_2011_a5_dy F u v = c * (- g v).

Theorem putnam_2011_a5
    (F : R -> R -> R)
    (g : R -> R)
    (Fgdiff :
      putnam_2011_a5_c2_bivariate F /\
      putnam_2011_a5_c2_univariate g)
    (prop1 : forall u : R, F u u = 0)
    (prop2 :
      forall x : R,
        g x > 0 /\ x ^ 2 * g x <= 1)
    (prop3 : putnam_2011_a5_gradient_condition F g) :
  exists C : R,
    forall n : nat,
      (2 <= n)%nat ->
      forall x : Fin.t (S n) -> R,
        exists i j : Fin.t (S n),
          i <> j /\
          Rabs (F (x i) (x j)) <= C / INR n.
Admitted.
