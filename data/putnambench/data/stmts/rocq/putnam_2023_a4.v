(* Statement-only formalization of PutnamBench corpus artifact putnam_2023_a4:
   integer combinations of the twelve normalized vertex vectors of a regular
   icosahedron are dense in real three-dimensional space. This file contains
   no proof. *)

From Stdlib Require Import Vectors.Fin ZArith Reals.

Open Scope R_scope.

Record putnam_2023_a4_vec3 : Type := {
  putnam_2023_a4_x : R;
  putnam_2023_a4_y : R;
  putnam_2023_a4_z : R
}.

Definition putnam_2023_a4_zero : putnam_2023_a4_vec3 :=
  {|
    putnam_2023_a4_x := 0;
    putnam_2023_a4_y := 0;
    putnam_2023_a4_z := 0
  |}.

Definition putnam_2023_a4_add
    (u v : putnam_2023_a4_vec3) : putnam_2023_a4_vec3 :=
  {|
    putnam_2023_a4_x := putnam_2023_a4_x u + putnam_2023_a4_x v;
    putnam_2023_a4_y := putnam_2023_a4_y u + putnam_2023_a4_y v;
    putnam_2023_a4_z := putnam_2023_a4_z u + putnam_2023_a4_z v
  |}.

Definition putnam_2023_a4_sub
    (u v : putnam_2023_a4_vec3) : putnam_2023_a4_vec3 :=
  {|
    putnam_2023_a4_x := putnam_2023_a4_x u - putnam_2023_a4_x v;
    putnam_2023_a4_y := putnam_2023_a4_y u - putnam_2023_a4_y v;
    putnam_2023_a4_z := putnam_2023_a4_z u - putnam_2023_a4_z v
  |}.

Definition putnam_2023_a4_scale
    (c : R) (u : putnam_2023_a4_vec3) : putnam_2023_a4_vec3 :=
  {|
    putnam_2023_a4_x := c * putnam_2023_a4_x u;
    putnam_2023_a4_y := c * putnam_2023_a4_y u;
    putnam_2023_a4_z := c * putnam_2023_a4_z u
  |}.

Definition putnam_2023_a4_norm
    (u : putnam_2023_a4_vec3) : R :=
  sqrt
    (putnam_2023_a4_x u ^ 2 +
     putnam_2023_a4_y u ^ 2 +
     putnam_2023_a4_z u ^ 2).

Record putnam_2023_a4_linear_isometry_equiv : Type := {
  putnam_2023_a4_iso_fun :
    putnam_2023_a4_vec3 -> putnam_2023_a4_vec3;
  putnam_2023_a4_iso_inv :
    putnam_2023_a4_vec3 -> putnam_2023_a4_vec3;
  putnam_2023_a4_iso_left_inverse :
    forall u,
      putnam_2023_a4_iso_inv (putnam_2023_a4_iso_fun u) = u;
  putnam_2023_a4_iso_right_inverse :
    forall u,
      putnam_2023_a4_iso_fun (putnam_2023_a4_iso_inv u) = u;
  putnam_2023_a4_iso_add :
    forall u v,
      putnam_2023_a4_iso_fun (putnam_2023_a4_add u v) =
      putnam_2023_a4_add
        (putnam_2023_a4_iso_fun u)
        (putnam_2023_a4_iso_fun v);
  putnam_2023_a4_iso_scale :
    forall (c : R) u,
      putnam_2023_a4_iso_fun (putnam_2023_a4_scale c u) =
      putnam_2023_a4_scale c (putnam_2023_a4_iso_fun u);
  putnam_2023_a4_iso_norm :
    forall u,
      putnam_2023_a4_norm (putnam_2023_a4_iso_fun u) =
      putnam_2023_a4_norm u
}.

Fixpoint putnam_2023_a4_fin_index
    {n : nat} (i : Fin.t n) : nat :=
  match i with
  | Fin.F1 => O
  | Fin.FS j => S (putnam_2023_a4_fin_index j)
  end.

Definition putnam_2023_a4_phi : R :=
  (1 + sqrt 5) / 2.

Definition putnam_2023_a4_vertex_nat
    (n : nat) : putnam_2023_a4_vec3 :=
  match n with
  | 0 =>
      {| putnam_2023_a4_x := 1;
         putnam_2023_a4_y := putnam_2023_a4_phi;
         putnam_2023_a4_z := 0 |}
  | 1 =>
      {| putnam_2023_a4_x := -1;
         putnam_2023_a4_y := putnam_2023_a4_phi;
         putnam_2023_a4_z := 0 |}
  | 2 =>
      {| putnam_2023_a4_x := 1;
         putnam_2023_a4_y := -putnam_2023_a4_phi;
         putnam_2023_a4_z := 0 |}
  | 3 =>
      {| putnam_2023_a4_x := -1;
         putnam_2023_a4_y := -putnam_2023_a4_phi;
         putnam_2023_a4_z := 0 |}
  | 4 =>
      {| putnam_2023_a4_x := putnam_2023_a4_phi;
         putnam_2023_a4_y := 0;
         putnam_2023_a4_z := 1 |}
  | 5 =>
      {| putnam_2023_a4_x := putnam_2023_a4_phi;
         putnam_2023_a4_y := 0;
         putnam_2023_a4_z := -1 |}
  | 6 =>
      {| putnam_2023_a4_x := -putnam_2023_a4_phi;
         putnam_2023_a4_y := 0;
         putnam_2023_a4_z := 1 |}
  | 7 =>
      {| putnam_2023_a4_x := -putnam_2023_a4_phi;
         putnam_2023_a4_y := 0;
         putnam_2023_a4_z := -1 |}
  | 8 =>
      {| putnam_2023_a4_x := 0;
         putnam_2023_a4_y := 1;
         putnam_2023_a4_z := putnam_2023_a4_phi |}
  | 9 =>
      {| putnam_2023_a4_x := 0;
         putnam_2023_a4_y := -1;
         putnam_2023_a4_z := putnam_2023_a4_phi |}
  | 10 =>
      {| putnam_2023_a4_x := 0;
         putnam_2023_a4_y := 1;
         putnam_2023_a4_z := -putnam_2023_a4_phi |}
  | 11 =>
      {| putnam_2023_a4_x := 0;
         putnam_2023_a4_y := -1;
         putnam_2023_a4_z := -putnam_2023_a4_phi |}
  | _ => putnam_2023_a4_zero
  end.

Definition putnam_2023_a4_vertex
    (i : Fin.t 12) : putnam_2023_a4_vec3 :=
  putnam_2023_a4_vertex_nat (putnam_2023_a4_fin_index i).

Definition putnam_2023_a4_normalizing_factor : R :=
  sqrt (1 + putnam_2023_a4_phi ^ 2).

Definition putnam_2023_a4_normalized_vertex
    (i : Fin.t 12) : putnam_2023_a4_vec3 :=
  putnam_2023_a4_scale
    (/ putnam_2023_a4_normalizing_factor)
    (putnam_2023_a4_vertex i).

Fixpoint putnam_2023_a4_fin_sum
    (n : nat) :
    (Fin.t n -> putnam_2023_a4_vec3) ->
    putnam_2023_a4_vec3 :=
  match n as k
        return
          (Fin.t k -> putnam_2023_a4_vec3) ->
          putnam_2023_a4_vec3
  with
  | O => fun _ => putnam_2023_a4_zero
  | S k =>
      fun f =>
        putnam_2023_a4_add
          (f Fin.F1)
          (putnam_2023_a4_fin_sum k
            (fun i => f (Fin.FS i)))
  end.

Theorem putnam_2023_a4
    (v : Fin.t 12 -> putnam_2023_a4_vec3)
    (hv :
      exists g : putnam_2023_a4_linear_isometry_equiv,
        forall i : Fin.t 12,
          putnam_2023_a4_iso_fun g (v i) =
          putnam_2023_a4_normalized_vertex i)
    (w : putnam_2023_a4_vec3)
    (epsilon : R)
    (hepsilon : epsilon > 0) :
  exists a : Fin.t 12 -> Z,
    putnam_2023_a4_norm
      (putnam_2023_a4_sub
        (putnam_2023_a4_fin_sum 12
          (fun i =>
            putnam_2023_a4_scale (IZR (a i)) (v i)))
        w) <
    epsilon.
Admitted.
