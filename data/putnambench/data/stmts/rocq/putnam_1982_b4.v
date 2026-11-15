(* Statement-only formalization of PutnamBench artifact putnam_1982_b4:
   divisibility of all integer translates of a finite product, the existence
   of an entry of absolute value one, and classification in the positive case.
   This file contains no proof. *)

From Stdlib Require Import ZArith Lists.List.

Import ListNotations.
Open Scope Z_scope.

Record putnam_1982_b4_finite_set := {
  putnam_1982_b4_elements : list Z;
  putnam_1982_b4_elements_nodup :
    NoDup putnam_1982_b4_elements
}.

Fixpoint putnam_1982_b4_product (xs : list Z) : Z :=
  match xs with
  | [] => 1
  | x :: rest => x * putnam_1982_b4_product rest
  end.

Definition putnam_1982_b4_condition
    (n : putnam_1982_b4_finite_set) : Prop :=
  (exists c : Z, In c (putnam_1982_b4_elements n)) /\
  forall k : Z,
    Z.divide
      (putnam_1982_b4_product (putnam_1982_b4_elements n))
      (putnam_1982_b4_product
        (map (fun i : Z => i + k) (putnam_1982_b4_elements n))).

Definition putnam_1982_b4_solution : Prop * Prop := (True, True).

Theorem putnam_1982_b4 :
  ((forall n : putnam_1982_b4_finite_set,
      putnam_1982_b4_condition n ->
      exists i : Z,
        In i (putnam_1982_b4_elements n) /\
        Z.abs i = 1)
    <-> fst putnam_1982_b4_solution) /\
  ((forall n : putnam_1982_b4_finite_set,
      putnam_1982_b4_condition n ->
      (forall i : Z,
        In i (putnam_1982_b4_elements n) ->
        0 < i) ->
      forall i : Z,
        In i (putnam_1982_b4_elements n) <->
        1 <= i <= Z.of_nat (length (putnam_1982_b4_elements n)))
    <-> snd putnam_1982_b4_solution).
Admitted.
