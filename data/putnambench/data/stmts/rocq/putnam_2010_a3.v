(* Statement-only formalization of PutnamBench corpus artifact putnam_2010_a3:
   a bounded continuously differentiable real function on the plane satisfying
   a constant-coefficient first-order partial differential equation vanishes
   identically. This file contains no proof. *)

From Stdlib Require Import Reals ClassicalEpsilon.

Open Scope R_scope.

Definition putnam_2010_a3_real_derivative
    (f : R -> R) (x : R) : R :=
  epsilon (inhabits (0 : R)) (fun d : R => derivable_pt_lim f x d).

Definition putnam_2010_a3_partial_x
    (h : (R * R)%type -> R) (p : (R * R)%type) : R :=
  putnam_2010_a3_real_derivative
    (fun x : R => h (x, snd p)) (fst p).

Definition putnam_2010_a3_partial_y
    (h : (R * R)%type -> R) (p : (R * R)%type) : R :=
  putnam_2010_a3_real_derivative
    (fun y : R => h (fst p, y)) (snd p).

Definition putnam_2010_a3_continuous_plane
    (f : (R * R)%type -> R) : Prop :=
  forall x y eps : R,
    eps > 0 ->
    exists delta : R,
      delta > 0 /\
      forall x' y' : R,
        Rabs (x' - x) < delta ->
        Rabs (y' - y) < delta ->
        Rabs (f (x', y') - f (x, y)) < eps.

Definition putnam_2010_a3_contdiff_one
    (h : (R * R)%type -> R) : Prop :=
  (forall x y : R,
    derivable_pt_lim
      (fun x' : R => h (x', y))
      x
      (putnam_2010_a3_partial_x h (x, y)) /\
    derivable_pt_lim
      (fun y' : R => h (x, y'))
      y
      (putnam_2010_a3_partial_y h (x, y))) /\
  putnam_2010_a3_continuous_plane
    (putnam_2010_a3_partial_x h) /\
  putnam_2010_a3_continuous_plane
    (putnam_2010_a3_partial_y h).

Theorem putnam_2010_a3
    (h : (R * R)%type -> R)
    (a b M : R)
    (H : putnam_2010_a3_contdiff_one h)
    (H' :
      forall p : (R * R)%type,
        h p =
        a * putnam_2010_a3_partial_x h p +
        b * putnam_2010_a3_partial_y h p)
    (H'' :
      forall p : (R * R)%type,
        Rabs (h p) <= M) :
  h = (fun _ : (R * R)%type => 0).
Admitted.
