(* Statement-only formalization of PutnamBench corpus artifact putnam_2024_a3
   (putnambench__rocq__putnam_2024_a3): among the increasing bijective
   fillings of a 3 by 2024 grid with 1 through 6072, some pair of positions is
   ordered in between one third and two thirds of the fillings. This file
   contains no proof. *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition putnam_2024_a3_row := 'I_3.
Definition putnam_2024_a3_column := 'I_2024.
Definition putnam_2024_a3_entry := 'I_6072.

Definition putnam_2024_a3_tableau :=
  {ffun (putnam_2024_a3_row * putnam_2024_a3_column) ->
    putnam_2024_a3_entry}.

Definition putnam_2024_a3_admissible
    (T : putnam_2024_a3_tableau) : bool :=
  [forall x : putnam_2024_a3_row * putnam_2024_a3_column,
    [forall y : putnam_2024_a3_row * putnam_2024_a3_column,
      (T x == T y) ==> (x == y)]] &&
  [forall v : putnam_2024_a3_entry,
    [exists x : putnam_2024_a3_row * putnam_2024_a3_column,
      T x == v]] &&
  [forall j : putnam_2024_a3_column,
    [forall i : putnam_2024_a3_row,
      [forall k : putnam_2024_a3_row,
        (i < k) ==> (T (i, j) < T (k, j))]]] &&
  [forall i : putnam_2024_a3_row,
    [forall j : putnam_2024_a3_column,
      [forall k : putnam_2024_a3_column,
        (j < k) ==> (T (i, j) < T (i, k))]]].

Definition putnam_2024_a3_S :=
  [set T : putnam_2024_a3_tableau |
    putnam_2024_a3_admissible T].

Definition putnam_2024_a3_favorable
    (a : putnam_2024_a3_row)
    (b : putnam_2024_a3_column)
    (c : putnam_2024_a3_row)
    (d : putnam_2024_a3_column) :=
  [set T : putnam_2024_a3_tableau |
    putnam_2024_a3_admissible T && (T (a, b) < T (c, d))].

Theorem putnam_2024_a3 :
  exists a : putnam_2024_a3_row,
  exists b : putnam_2024_a3_column,
  exists c : putnam_2024_a3_row,
  exists d : putnam_2024_a3_column,
    (0 < #|putnam_2024_a3_S|)%nat /\
    (#|putnam_2024_a3_S| <=
       3 * #|putnam_2024_a3_favorable a b c d|)%nat /\
    (3 * #|putnam_2024_a3_favorable a b c d| <=
       2 * #|putnam_2024_a3_S|)%nat.
Admitted.
