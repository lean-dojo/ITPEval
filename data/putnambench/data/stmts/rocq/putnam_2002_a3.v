(* Statement-only formalization of PutnamBench corpus artifact putnam_2002_a3:
   parity of the number of nonempty subsets of an initial integer interval
   whose average is an integer. This file contains no proof. *)

From Stdlib Require Import Reals List Sorting.Sorted ZArith.

Open Scope Z_scope.

Fixpoint putnam_2002_a3_sum (xs : list Z) : Z :=
  match xs with
  | nil => 0
  | cons x tail => x + putnam_2002_a3_sum tail
  end.

Definition putnam_2002_a3_qualifying_subset
    (n : Z) (xs : list Z) : Prop :=
  StronglySorted Z.lt xs /\
  xs <> nil /\
  Forall (fun x : Z => 1 <= x <= n) xs /\
  exists k : Z,
    (IZR (putnam_2002_a3_sum xs) / INR (length xs))%R = IZR k.

Definition putnam_2002_a3_has_integer_cardinality
    (P : list Z -> Prop) (cardinality : Z) : Prop :=
  exists enumeration : list (list Z),
    NoDup enumeration /\
    (forall xs : list Z, In xs enumeration <-> P xs) /\
    cardinality = Z.of_nat (length enumeration).

Theorem putnam_2002_a3
    (n Tn : Z)
    (hn : 2 <= n)
    (hTn :
      putnam_2002_a3_has_integer_cardinality
        (putnam_2002_a3_qualifying_subset n) Tn) :
  Z.Even (Tn - n).
Admitted.
