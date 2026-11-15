(* Statement-only formalization of PutnamBench corpus artifact putnam_2013_a2:
   injectivity of the least attainable final term in an increasing integer
   sequence whose product with a positive nonsquare is a square. This file
   contains no proof. *)

From Stdlib Require Import ZArith Lists.List.

Open Scope Z_scope.

Fixpoint putnam_2013_a2_product (values : list Z) : Z :=
  match values with
  | nil => 1
  | value :: rest => value * putnam_2013_a2_product rest
  end.

Fixpoint putnam_2013_a2_strictly_increasing
    (values : list Z) : Prop :=
  match values with
  | nil => True
  | value :: rest =>
      match rest with
      | nil => True
      | next :: _ =>
          value < next /\
          putnam_2013_a2_strictly_increasing rest
      end
  end.

Definition putnam_2013_a2_nonsquare (n : Z) : Prop :=
  0 < n /\ ~ exists root : Z, root ^ 2 = n.

Definition putnam_2013_a2_qualifying_sequence
    (n : Z) (values : list Z) : Prop :=
  match values with
  | nil => False
  | first :: _ =>
      n < first /\
      (exists root : Z,
        root ^ 2 = n * putnam_2013_a2_product values) /\
      putnam_2013_a2_strictly_increasing values
  end.

Definition putnam_2013_a2_attainable_last
    (n last_value : Z) : Prop :=
  exists values : list Z,
    putnam_2013_a2_qualifying_sequence n values /\
    List.last values 0 = last_value.

Theorem putnam_2013_a2 :
  forall f : Z -> Z,
    (forall n : Z,
      putnam_2013_a2_nonsquare n ->
      putnam_2013_a2_attainable_last n (f n) /\
      forall last_value : Z,
        putnam_2013_a2_attainable_last n last_value ->
        f n <= last_value) ->
    forall x y : Z,
      putnam_2013_a2_nonsquare x ->
      putnam_2013_a2_nonsquare y ->
      f x = f y ->
      x = y.
Admitted.
