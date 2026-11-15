(* Statement-only formalization of PutnamBench artifact putnam_1973_a6:
   seven distinct real plane lines cannot have at least six points incident
   with exactly three lines and at least four points incident with exactly
   two. This file contains no proof. *)

From Stdlib Require Import Vectors.Fin Reals Ensembles Finite_sets.

Open Scope R_scope.

Definition putnam_1973_a6_index : Type := Fin.t 7.
Definition putnam_1973_a6_point : Type := (R * R)%type.
Definition putnam_1973_a6_line : Type := (R * R)%type.

Definition putnam_1973_a6_on_line
    (p : putnam_1973_a6_point)
    (line : putnam_1973_a6_line) : Prop :=
  snd p = fst line * fst p + snd line.

Definition putnam_1973_a6_on_all
    (lines : putnam_1973_a6_index -> putnam_1973_a6_line)
    (indices : Ensemble putnam_1973_a6_index)
    (p : putnam_1973_a6_point) : Prop :=
  forall i : putnam_1973_a6_index,
    In putnam_1973_a6_index indices i ->
    putnam_1973_a6_on_line p (lines i).

Definition putnam_1973_a6_nfold_point
    (n : nat)
    (lines : putnam_1973_a6_index -> putnam_1973_a6_line)
    (p : putnam_1973_a6_point) : Prop :=
  exists indices : Ensemble putnam_1973_a6_index,
    cardinal putnam_1973_a6_index indices n /\
    putnam_1973_a6_on_all lines indices p /\
    forall other : Ensemble putnam_1973_a6_index,
      cardinal putnam_1973_a6_index other n ->
      putnam_1973_a6_on_all lines other p ->
      Same_set putnam_1973_a6_index indices other.

Definition putnam_1973_a6_at_least
    (n lower : nat)
    (lines : putnam_1973_a6_index -> putnam_1973_a6_line) : Prop :=
  exists total : nat,
    cardinal
      putnam_1973_a6_point
      (putnam_1973_a6_nfold_point n lines)
      total /\
    (lower <= total)%nat.

Theorem putnam_1973_a6 :
  ~ exists lines : putnam_1973_a6_index -> putnam_1973_a6_line,
      (forall i j : putnam_1973_a6_index,
        i <> j ->
        lines i <> lines j) /\
      putnam_1973_a6_at_least 3 6 lines /\
      putnam_1973_a6_at_least 2 4 lines.
Admitted.
