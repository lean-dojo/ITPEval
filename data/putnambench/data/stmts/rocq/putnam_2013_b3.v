(* Statement-only formalization of PutnamBench corpus artifact putnam_2013_b3:
   additive representation of a real-valued valuation on a finite lattice of
   subsets satisfying a one-element deletion condition. This file contains no
   proof. *)

From Stdlib Require Import Reals Lists.List Vectors.Vector.

Open Scope R_scope.

Definition putnam_2013_b3_subset (n : nat) : Type :=
  Vector.t bool n.

Definition putnam_2013_b3_empty (n : nat) :
    putnam_2013_b3_subset n :=
  Vector.const false n.

Definition putnam_2013_b3_union
    {n : nat}
    (S T : putnam_2013_b3_subset n) :
    putnam_2013_b3_subset n :=
  Vector.map2 orb S T.

Definition putnam_2013_b3_intersection
    {n : nat}
    (S T : putnam_2013_b3_subset n) :
    putnam_2013_b3_subset n :=
  Vector.map2 andb S T.

Definition putnam_2013_b3_subseteq
    {n : nat}
    (S T : putnam_2013_b3_subset n) : Prop :=
  forall i : Fin.t n,
    Vector.nth S i = true ->
    Vector.nth T i = true.

Definition putnam_2013_b3_proper_subset
    {n : nat}
    (S T : putnam_2013_b3_subset n) : Prop :=
  putnam_2013_b3_subseteq S T /\ S <> T.

Definition putnam_2013_b3_card
    {n : nat}
    (S : putnam_2013_b3_subset n) : nat :=
  Vector.fold_left
    (fun (count : nat) (present : bool) =>
      if present then Nat.succ count else count)
    0%nat S.

Definition putnam_2013_b3_weighted_sum
    {n : nat}
    (S : putnam_2013_b3_subset n)
    (weights : Vector.t R n) : R :=
  Vector.fold_left2
    (fun (total : R) (present : bool) (weight : R) =>
      if present then total + weight else total)
    0 S weights.

Definition putnam_2013_b3_solution : Prop := True.

Theorem putnam_2013_b3 :
  (forall
      (n : nat)
      (P : list (putnam_2013_b3_subset n))
      (f : putnam_2013_b3_subset n -> R),
      P <> List.nil ->
      (forall S T : putnam_2013_b3_subset n,
        List.In S P ->
        List.In T P ->
        List.In (putnam_2013_b3_union S T) P /\
        List.In (putnam_2013_b3_intersection S T) P) ->
      (forall S : putnam_2013_b3_subset n,
        List.In S P ->
        S <> putnam_2013_b3_empty n ->
        exists T : putnam_2013_b3_subset n,
          List.In T P /\
          putnam_2013_b3_proper_subset T S /\
          (putnam_2013_b3_card T + 1 =
           putnam_2013_b3_card S)%nat) ->
      f (putnam_2013_b3_empty n) = 0 ->
      (forall S T : putnam_2013_b3_subset n,
        List.In S P ->
        List.In T P ->
        f (putnam_2013_b3_union S T) =
          f S + f T - f (putnam_2013_b3_intersection S T)) ->
      exists weights : Vector.t R n,
        forall S : putnam_2013_b3_subset n,
          List.In S P ->
          f S = putnam_2013_b3_weighted_sum S weights) <->
  putnam_2013_b3_solution.
Admitted.
