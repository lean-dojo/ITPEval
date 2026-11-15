(* Statement-only formalization of PutnamBench corpus artifact putnam_2021_a1:
   the least number of length-5 hops between integer lattice points needed
   to travel from (0, 0) to (2021, 2021). This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List ZArith.ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition putnam_2021_a1_point : Type := (Z * Z)%type.

Definition putnam_2021_a1_hop
    (p q : putnam_2021_a1_point) : Prop :=
  (fst q - fst p) ^ 2 + (snd q - snd p) ^ 2 = 25.

Fixpoint putnam_2021_a1_successive_hops
    (p : putnam_2021_a1_point)
    (remaining : list putnam_2021_a1_point) : Prop :=
  match remaining with
  | [] => True
  | q :: rest =>
      putnam_2021_a1_hop p q /\
      putnam_2021_a1_successive_hops q rest
  end.

Definition putnam_2021_a1_reaches_in (k : nat) : Prop :=
  exists remaining : list putnam_2021_a1_point,
    length remaining = k /\
    putnam_2021_a1_successive_hops (0, 0) remaining /\
    List.last remaining (0, 0) = (2021, 2021).

Definition putnam_2021_a1_solution : nat := 578.

Theorem putnam_2021_a1 :
  putnam_2021_a1_reaches_in putnam_2021_a1_solution /\
  forall k : nat,
    putnam_2021_a1_reaches_in k ->
    (putnam_2021_a1_solution <= k)%nat.
Admitted.
