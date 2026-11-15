(* Statement-only formalization of PutnamBench corpus artifact putnam_1995_b1:
   for any two partitions of a nine-element set, two distinct elements have
   containing parts of the same size in both partitions. This file contains
   no proof. *)

From Stdlib Require Import Lists.List Vectors.Fin ClassicalDescription.

Record putnam_1995_b1_partition : Type := {
  putnam_1995_b1_equiv : Fin.t 9 -> Fin.t 9 -> Prop;
  putnam_1995_b1_equiv_refl :
    forall x : Fin.t 9, putnam_1995_b1_equiv x x;
  putnam_1995_b1_equiv_sym :
    forall x y : Fin.t 9,
      putnam_1995_b1_equiv x y ->
      putnam_1995_b1_equiv y x;
  putnam_1995_b1_equiv_trans :
    forall x y z : Fin.t 9,
      putnam_1995_b1_equiv x y ->
      putnam_1995_b1_equiv y z ->
      putnam_1995_b1_equiv x z
}.

Fixpoint putnam_1995_b1_indices (n : nat) : list (Fin.t n) :=
  match n with
  | O => nil
  | S k => Fin.F1 :: map Fin.FS (putnam_1995_b1_indices k)
  end.

Definition putnam_1995_b1_same_partb
    (partition : putnam_1995_b1_partition)
    (x y : Fin.t 9) : bool :=
  if excluded_middle_informative
       (putnam_1995_b1_equiv partition x y)
  then true
  else false.

Definition putnam_1995_b1_part_size
    (partition : putnam_1995_b1_partition)
    (x : Fin.t 9) : nat :=
  length
    (filter
      (putnam_1995_b1_same_partb partition x)
      (putnam_1995_b1_indices 9)).

Theorem putnam_1995_b1 :
  forall Pt1 Pt2 : putnam_1995_b1_partition,
    exists x y : Fin.t 9,
      x <> y /\
      putnam_1995_b1_part_size Pt1 x =
        putnam_1995_b1_part_size Pt1 y /\
      putnam_1995_b1_part_size Pt2 x =
        putnam_1995_b1_part_size Pt2 y.
Admitted.
