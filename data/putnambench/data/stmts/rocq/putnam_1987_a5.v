(* Statement-only formalization of PutnamBench artifact putnam_1987_a5:
   nonexistence of a continuously partially differentiable curl-free vector
   field on punctured three-space with a prescribed trace on the coordinate
   plane; this file contains no proof. *)

From Stdlib Require Import
  Reals
  ClassicalDescription
  ClassicalEpsilon.

Open Scope R_scope.

Inductive putnam_1987_a5_coordinate : Type :=
  | putnam_1987_a5_x
  | putnam_1987_a5_y
  | putnam_1987_a5_z.

Record putnam_1987_a5_vector : Type := {
  putnam_1987_a5_vector_x : R;
  putnam_1987_a5_vector_y : R;
  putnam_1987_a5_vector_z : R
}.

Definition putnam_1987_a5_vector_of
    (x y z : R) : putnam_1987_a5_vector :=
  {|
    putnam_1987_a5_vector_x := x;
    putnam_1987_a5_vector_y := y;
    putnam_1987_a5_vector_z := z
  |}.

Definition putnam_1987_a5_component
    (v : putnam_1987_a5_vector)
    (i : putnam_1987_a5_coordinate) : R :=
  match i with
  | putnam_1987_a5_x => putnam_1987_a5_vector_x v
  | putnam_1987_a5_y => putnam_1987_a5_vector_y v
  | putnam_1987_a5_z => putnam_1987_a5_vector_z v
  end.

Definition putnam_1987_a5_zero : putnam_1987_a5_vector :=
  putnam_1987_a5_vector_of 0 0 0.

Definition putnam_1987_a5_replace
    (v : putnam_1987_a5_vector)
    (i : putnam_1987_a5_coordinate)
    (value : R) : putnam_1987_a5_vector :=
  match i with
  | putnam_1987_a5_x =>
      putnam_1987_a5_vector_of
        value
        (putnam_1987_a5_vector_y v)
        (putnam_1987_a5_vector_z v)
  | putnam_1987_a5_y =>
      putnam_1987_a5_vector_of
        (putnam_1987_a5_vector_x v)
        value
        (putnam_1987_a5_vector_z v)
  | putnam_1987_a5_z =>
      putnam_1987_a5_vector_of
        (putnam_1987_a5_vector_x v)
        (putnam_1987_a5_vector_y v)
        value
  end.

Definition putnam_1987_a5_distance
    (u v : putnam_1987_a5_vector) : R :=
  sqrt
    ((putnam_1987_a5_vector_x u - putnam_1987_a5_vector_x v) ^ 2 +
     (putnam_1987_a5_vector_y u - putnam_1987_a5_vector_y v) ^ 2 +
     (putnam_1987_a5_vector_z u - putnam_1987_a5_vector_z v) ^ 2).

Definition putnam_1987_a5_real_derivative
    (f : R -> R) (x : R) : R :=
  match excluded_middle_informative
          (exists d : R, derivable_pt_lim f x d) with
  | left _ =>
      epsilon (inhabits 0)
        (fun d : R => derivable_pt_lim f x d)
  | right _ => 0
  end.

Definition putnam_1987_a5_partial_derivative
    (f : putnam_1987_a5_vector -> R)
    (i : putnam_1987_a5_coordinate)
    (v : putnam_1987_a5_vector) : R :=
  putnam_1987_a5_real_derivative
    (fun value : R =>
      f (putnam_1987_a5_replace v i value))
    (putnam_1987_a5_component v i).

Definition putnam_1987_a5_continuous_on_punctured
    (f : putnam_1987_a5_vector -> R) : Prop :=
  forall v : putnam_1987_a5_vector,
    v <> putnam_1987_a5_zero ->
    forall eps : R,
      eps > 0 ->
      exists delta : R,
        delta > 0 /\
        forall w : putnam_1987_a5_vector,
          w <> putnam_1987_a5_zero ->
          putnam_1987_a5_distance w v < delta ->
          Rabs (f w - f v) < eps.

Definition putnam_1987_a5_continuously_partially_differentiable
    (F : putnam_1987_a5_vector -> putnam_1987_a5_vector) : Prop :=
  (forall
      (output input : putnam_1987_a5_coordinate)
      (v : putnam_1987_a5_vector),
      v <> putnam_1987_a5_zero ->
      derivable_pt_lim
        (fun value : R =>
          putnam_1987_a5_component
            (F (putnam_1987_a5_replace v input value))
            output)
        (putnam_1987_a5_component v input)
        (putnam_1987_a5_partial_derivative
          (fun w : putnam_1987_a5_vector =>
            putnam_1987_a5_component (F w) output)
          input v)) /\
  (forall output input : putnam_1987_a5_coordinate,
      putnam_1987_a5_continuous_on_punctured
        (fun v : putnam_1987_a5_vector =>
          putnam_1987_a5_partial_derivative
            (fun w : putnam_1987_a5_vector =>
              putnam_1987_a5_component (F w) output)
            input v)).

Definition putnam_1987_a5_curl
    (F : putnam_1987_a5_vector -> putnam_1987_a5_vector)
    (v : putnam_1987_a5_vector) : putnam_1987_a5_vector :=
  putnam_1987_a5_vector_of
    (putnam_1987_a5_partial_derivative
       (fun w =>
         putnam_1987_a5_vector_z (F w))
       putnam_1987_a5_y v -
     putnam_1987_a5_partial_derivative
       (fun w =>
         putnam_1987_a5_vector_y (F w))
       putnam_1987_a5_z v)
    (putnam_1987_a5_partial_derivative
       (fun w =>
         putnam_1987_a5_vector_x (F w))
       putnam_1987_a5_z v -
     putnam_1987_a5_partial_derivative
       (fun w =>
         putnam_1987_a5_vector_z (F w))
       putnam_1987_a5_x v)
    (putnam_1987_a5_partial_derivative
       (fun w =>
         putnam_1987_a5_vector_y (F w))
       putnam_1987_a5_x v -
     putnam_1987_a5_partial_derivative
       (fun w =>
         putnam_1987_a5_vector_x (F w))
       putnam_1987_a5_y v).

Definition putnam_1987_a5_G
    (x y : R) : putnam_1987_a5_vector :=
  putnam_1987_a5_vector_of
    (- y / (x ^ 2 + 4 * y ^ 2))
    (x / (x ^ 2 + 4 * y ^ 2))
    0.

Definition putnam_1987_a5_solution : Prop := False.

Theorem putnam_1987_a5 :
  ((exists F : putnam_1987_a5_vector -> putnam_1987_a5_vector,
      putnam_1987_a5_continuously_partially_differentiable F /\
      (forall v : putnam_1987_a5_vector,
        v <> putnam_1987_a5_zero ->
        putnam_1987_a5_curl F v = putnam_1987_a5_zero) /\
      (forall x y : R,
        F (putnam_1987_a5_vector_of x y 0) =
        putnam_1987_a5_G x y)) <->
   putnam_1987_a5_solution).
Admitted.
