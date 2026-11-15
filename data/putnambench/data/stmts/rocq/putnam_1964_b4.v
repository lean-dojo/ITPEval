(* Statement-only formalization of PutnamBench artifact putnam_1964_b4:
   counting the regions cut on the unit sphere by great circles in general
   position. This file contains no proof. *)

From Stdlib Require Import Vectors.Fin Reals Ensembles Finite_sets List.

Open Scope R_scope.

Record putnam_1964_b4_point : Type := {
  putnam_1964_b4_x : R;
  putnam_1964_b4_y : R;
  putnam_1964_b4_z : R
}.

Definition putnam_1964_b4_point_set : Type :=
  putnam_1964_b4_point -> Prop.

Definition putnam_1964_b4_zero : putnam_1964_b4_point :=
  {| putnam_1964_b4_x := 0;
     putnam_1964_b4_y := 0;
     putnam_1964_b4_z := 0 |}.

Definition putnam_1964_b4_dot
    (u w : putnam_1964_b4_point) : R :=
  putnam_1964_b4_x u * putnam_1964_b4_x w +
  putnam_1964_b4_y u * putnam_1964_b4_y w +
  putnam_1964_b4_z u * putnam_1964_b4_z w.

Definition putnam_1964_b4_sphere : putnam_1964_b4_point_set :=
  fun p : putnam_1964_b4_point =>
    putnam_1964_b4_dot p p = 1.

Definition putnam_1964_b4_same_set
    (A B : putnam_1964_b4_point_set) : Prop :=
  forall p : putnam_1964_b4_point, A p <-> B p.

Definition putnam_1964_b4_intersection
    (A B : putnam_1964_b4_point_set) : putnam_1964_b4_point_set :=
  fun p : putnam_1964_b4_point => A p /\ B p.

Inductive putnam_1964_b4_sign : Type :=
| putnam_1964_b4_negative
| putnam_1964_b4_zero_sign
| putnam_1964_b4_positive.

Definition putnam_1964_b4_sign_of_real
    (r : R) : putnam_1964_b4_sign :=
  if Rlt_dec r 0 then
    putnam_1964_b4_negative
  else if Rlt_dec 0 r then
    putnam_1964_b4_positive
  else
    putnam_1964_b4_zero_sign.

Definition putnam_1964_b4_circle_indices
    {n : nat}
    (C : Fin.t n -> putnam_1964_b4_point_set)
    (p q : putnam_1964_b4_point) : Ensemble (Fin.t n) :=
  fun i : Fin.t n => C i p /\ C i q.

Fixpoint putnam_1964_b4_no_duplicate_sets
    (sets : list putnam_1964_b4_point_set) : Prop :=
  match sets with
  | nil => True
  | first :: rest =>
      (forall other : putnam_1964_b4_point_set,
        List.In other rest ->
        ~ putnam_1964_b4_same_set first other) /\
      putnam_1964_b4_no_duplicate_sets rest
  end.

Definition putnam_1964_b4_has_cardinality
    (collection : putnam_1964_b4_point_set -> Prop)
    (size : nat) : Prop :=
  exists representatives : list putnam_1964_b4_point_set,
    List.length representatives = size /\
    putnam_1964_b4_no_duplicate_sets representatives /\
    forall region : putnam_1964_b4_point_set,
      collection region <->
      exists representative : putnam_1964_b4_point_set,
        List.In representative representatives /\
        putnam_1964_b4_same_set region representative.

Definition putnam_1964_b4_solution (n : nat) : nat :=
  (n * n - n + 2)%nat.

Theorem putnam_1964_b4
    {n : nat}
    (hn : (0 < n)%nat)
    (C : Fin.t n -> putnam_1964_b4_point_set)
    (v : Fin.t n -> putnam_1964_b4_point)
    (hv :
      forall i : Fin.t n,
        putnam_1964_b4_same_set
          (C i)
          (putnam_1964_b4_intersection
            putnam_1964_b4_sphere
            (fun p : putnam_1964_b4_point =>
              putnam_1964_b4_dot (v i) p = 0)))
    (hv_nonzero :
      forall i : Fin.t n, v i <> putnam_1964_b4_zero)
    (hC_injective :
      forall i j : Fin.t n,
        putnam_1964_b4_same_set (C i) (C j) ->
        i = j)
    (h_general_position :
      forall p q : putnam_1964_b4_point,
        putnam_1964_b4_sphere p ->
        putnam_1964_b4_sphere q ->
        exists k : nat,
          cardinal
            (Fin.t n)
            (putnam_1964_b4_circle_indices C p q)
            k /\
          (k <= 2)%nat)
    (IsRegion : putnam_1964_b4_point_set -> Prop)
    (IsRegion_def :
      forall region : putnam_1964_b4_point_set,
        IsRegion region <->
        (exists p : putnam_1964_b4_point, region p) /\
        exists sign : Fin.t n -> putnam_1964_b4_sign,
          (forall i : Fin.t n,
            sign i <> putnam_1964_b4_zero_sign) /\
          putnam_1964_b4_same_set
            region
            (putnam_1964_b4_intersection
              putnam_1964_b4_sphere
              (fun p : putnam_1964_b4_point =>
                forall i : Fin.t n,
                  putnam_1964_b4_sign_of_real
                    (putnam_1964_b4_dot (v i) p) =
                  sign i))) :
  putnam_1964_b4_has_cardinality
    (fun region : putnam_1964_b4_point_set => IsRegion region)
    (putnam_1964_b4_solution n).
Admitted.
