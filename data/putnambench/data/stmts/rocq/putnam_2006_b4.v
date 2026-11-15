(* Statement-only formalization of PutnamBench corpus artifact putnam_2006_b4:
   the maximum number of Boolean-cube vertices lying in a k-dimensional real
   linear subspace of R^n is 2^k. This file contains no proof. *)

From Stdlib Require Import Reals Lists.List Vectors.Fin Arith.PeanoNat.

Open Scope R_scope.

Definition putnam_2006_b4_vector (n : nat) : Type :=
  Fin.t n -> RbaseSymbolsImpl.R.

Definition putnam_2006_b4_vector_eq {n : nat}
    (u v : putnam_2006_b4_vector n) : Prop :=
  forall i : Fin.t n, u i = v i.

Definition putnam_2006_b4_zero {n : nat} :
    putnam_2006_b4_vector n :=
  fun _ => 0.

Definition putnam_2006_b4_add {n : nat}
    (u v : putnam_2006_b4_vector n) :
    putnam_2006_b4_vector n :=
  fun i => u i + v i.

Definition putnam_2006_b4_scale {n : nat}
    (a : RbaseSymbolsImpl.R) (v : putnam_2006_b4_vector n) :
    putnam_2006_b4_vector n :=
  fun i => a * v i.

Fixpoint putnam_2006_b4_linear_combination {n : nat}
    (coefficients : list RbaseSymbolsImpl.R)
    (vectors : list (putnam_2006_b4_vector n)) :
    putnam_2006_b4_vector n :=
  match coefficients, vectors with
  | a :: coefficients', v :: vectors' =>
      putnam_2006_b4_add
        (putnam_2006_b4_scale a v)
        (putnam_2006_b4_linear_combination coefficients' vectors')
  | _, _ => putnam_2006_b4_zero
  end.

Definition putnam_2006_b4_is_subspace {n : nat}
    (V : putnam_2006_b4_vector n -> Prop) : Prop :=
  (forall u v,
    putnam_2006_b4_vector_eq u v ->
    V u ->
    V v) /\
  V putnam_2006_b4_zero /\
  (forall u v,
    V u ->
    V v ->
    V (putnam_2006_b4_add u v)) /\
  (forall (a : RbaseSymbolsImpl.R) v,
    V v ->
    V (putnam_2006_b4_scale a v)).

Definition putnam_2006_b4_linearly_independent {n : nat}
    (vectors : list (putnam_2006_b4_vector n)) : Prop :=
  forall coefficients : list RbaseSymbolsImpl.R,
    length coefficients = length vectors ->
    putnam_2006_b4_vector_eq
      (putnam_2006_b4_linear_combination coefficients vectors)
      putnam_2006_b4_zero ->
    Forall (fun coefficient => coefficient = 0) coefficients.

Definition putnam_2006_b4_spans {n : nat}
    (V : putnam_2006_b4_vector n -> Prop)
    (vectors : list (putnam_2006_b4_vector n)) : Prop :=
  forall v : putnam_2006_b4_vector n,
    V v ->
    exists coefficients : list RbaseSymbolsImpl.R,
      length coefficients = length vectors /\
      putnam_2006_b4_vector_eq
        (putnam_2006_b4_linear_combination coefficients vectors)
        v.

Definition putnam_2006_b4_has_dimension {n : nat}
    (V : putnam_2006_b4_vector n -> Prop)
    (k : nat) : Prop :=
  putnam_2006_b4_is_subspace V /\
  exists basis : list (putnam_2006_b4_vector n),
    length basis = k /\
    (forall v, In v basis -> V v) /\
    putnam_2006_b4_linearly_independent basis /\
    putnam_2006_b4_spans V basis.

Definition putnam_2006_b4_boolean_vertex {n : nat}
    (v : putnam_2006_b4_vector n) : Prop :=
  forall i : Fin.t n, v i = 0 \/ v i = 1.

Definition putnam_2006_b4_has_cardinality {n : nat}
    (members : putnam_2006_b4_vector n -> Prop)
    (cardinality : nat) : Prop :=
  exists enumeration :
      Fin.t cardinality -> putnam_2006_b4_vector n,
    (forall i j,
      putnam_2006_b4_vector_eq (enumeration i) (enumeration j) ->
      i = j) /\
    (forall v,
      members v <->
      exists i, putnam_2006_b4_vector_eq (enumeration i) v).

Definition putnam_2006_b4_intersection_counts
    (n k : nat) (count : nat) : Prop :=
  exists V : putnam_2006_b4_vector n -> Prop,
    putnam_2006_b4_has_dimension V k /\
    putnam_2006_b4_has_cardinality
      (fun v => putnam_2006_b4_boolean_vertex v /\ V v)
      count.

Definition putnam_2006_b4_is_greatest
    (values : nat -> Prop) (maximum : nat) : Prop :=
  values maximum /\
  forall value : nat, values value -> (value <= maximum)%nat.

Definition putnam_2006_b4_solution (k : nat) : nat :=
  Nat.pow 2 k.

Theorem putnam_2006_b4
    (n k : nat)
    (npos : (0 < n)%nat)
    (hk : (k <= n)%nat) :
  putnam_2006_b4_is_greatest
    (putnam_2006_b4_intersection_counts n k)
    (putnam_2006_b4_solution k).
Admitted.
