(* Statement-only formalization of PutnamBench corpus artifact putnam_1996_b5:
   the number of two-symbol strings whose every consecutive substring has
   symbol-count imbalance between -2 and 2. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Vectors.Fin
  ZArith.

Open Scope Z_scope.

Fixpoint putnam_1996_b5_fin_sum
    (n : nat) : (Fin.t n -> Z) -> Z :=
  match n as m return (Fin.t m -> Z) -> Z with
  | O => fun _ => 0
  | S k =>
      fun f =>
        f Fin.F1 +
        putnam_1996_b5_fin_sum k (fun i => f (Fin.FS i))
  end.

Definition putnam_1996_b5_index
    {n : nat} (i : Fin.t n) : nat :=
  proj1_sig (Fin.to_nat i).

Definition putnam_1996_b5_delta
    {n : nat} (S : Fin.t n -> bool) (a b : Fin.t n) : Z :=
  putnam_1996_b5_fin_sum n
    (fun i =>
      if andb
           (Nat.leb (putnam_1996_b5_index a)
                    (putnam_1996_b5_index i))
           (Nat.leb (putnam_1996_b5_index i)
                    (putnam_1996_b5_index b))
      then if S i then 1 else -1
      else 0).

Definition putnam_1996_b5_balanced
    {n : nat} (S : Fin.t n -> bool) : Prop :=
  forall a b : Fin.t n,
    (putnam_1996_b5_index a <= putnam_1996_b5_index b)%nat ->
    (-2 <= putnam_1996_b5_delta S a b /\
     putnam_1996_b5_delta S a b <= 2)%Z.

Definition putnam_1996_b5_string_eq
    {n : nat} (S T : Fin.t n -> bool) : Prop :=
  forall i : Fin.t n, S i = T i.

Fixpoint putnam_1996_b5_distinct_representatives
    {n : nat} (strings : list (Fin.t n -> bool)) : Prop :=
  match strings with
  | nil => True
  | head :: remaining =>
      (forall T : Fin.t n -> bool,
          In T remaining ->
          ~ putnam_1996_b5_string_eq head T) /\
      putnam_1996_b5_distinct_representatives remaining
  end.

Definition putnam_1996_b5_has_cardinality
    (n : nat)
    (P : (Fin.t n -> bool) -> Prop)
    (cardinality : nat) : Prop :=
  exists representatives : list (Fin.t n -> bool),
    length representatives = cardinality /\
    putnam_1996_b5_distinct_representatives representatives /\
    forall S : Fin.t n -> bool,
      P S <->
      exists T : Fin.t n -> bool,
        In T representatives /\
        putnam_1996_b5_string_eq S T.

Definition putnam_1996_b5_solution (n : nat) : nat :=
  (Nat.pow 2 (Nat.div (n + 2) 2) +
   Nat.pow 2 (Nat.div (n + 1) 2) - 2)%nat.

Theorem putnam_1996_b5 (n : nat) :
  putnam_1996_b5_has_cardinality
    n
    (fun S => putnam_1996_b5_balanced S)
    (putnam_1996_b5_solution n).
Admitted.
