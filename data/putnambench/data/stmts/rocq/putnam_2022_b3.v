(* Statement-only formalization of PutnamBench corpus artifact putnam_2022_b3:
   finite iteration of the same-color distance recoloring operation on the
   positive real numbers. This file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition putnam_2022_b3_coloring : Type :=
  R -> Prop.

Definition putnam_2022_b3_recolor
    (isred : putnam_2022_b3_coloring) :
    putnam_2022_b3_coloring :=
  fun d : R =>
    exists p q : R,
      0 < p /\
      0 < q /\
      p < q /\
      (isred p <-> isred q) /\
      q - p = d.

Fixpoint putnam_2022_b3_iterate
    (k : nat)
    (isred : putnam_2022_b3_coloring) :
    putnam_2022_b3_coloring :=
  match k with
  | O => isred
  | S n =>
      putnam_2022_b3_recolor
        (putnam_2022_b3_iterate n isred)
  end.

Definition putnam_2022_b3_solution : Prop :=
  True.

Theorem putnam_2022_b3 :
  (forall isred : putnam_2022_b3_coloring,
      exists k : nat,
        forall p : R,
          0 < p ->
          putnam_2022_b3_iterate k isred p) <->
  putnam_2022_b3_solution.
Admitted.
