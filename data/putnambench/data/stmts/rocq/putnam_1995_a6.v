(* Statement-only formalization of PutnamBench corpus artifact putnam_1995_a6:
   counting 3 by n integer matrices whose columns are permutations of
   1, 2, 3, comparing consecutive row sums with equal row sums; this file
   contains no proof. *)

From Stdlib Require Import ZArith.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition putnam_1995_a6_entry {n : nat}
    (M : {ffun 'I_n -> 'I_6}) (i : 'I_3) (j : 'I_n) : Z :=
  let row := nat_of_ord i in
  match nat_of_ord (M j) with
  | O =>
      Z.of_nat (S row)
  | S O =>
      match row with
      | O => 1%Z
      | S O => 3%Z
      | _ => 2%Z
      end
  | S (S O) =>
      match row with
      | O => 2%Z
      | S O => 1%Z
      | _ => 3%Z
      end
  | S (S (S O)) =>
      match row with
      | O => 2%Z
      | S O => 3%Z
      | _ => 1%Z
      end
  | S (S (S (S O))) =>
      match row with
      | O => 3%Z
      | S O => 1%Z
      | _ => 2%Z
      end
  | _ =>
      match row with
      | O => 3%Z
      | S O => 2%Z
      | _ => 1%Z
      end
  end.

Fixpoint putnam_1995_a6_sum_columns {n : nat}
    (M : {ffun 'I_n -> 'I_6}) (i : 'I_3)
    (columns : seq 'I_n) : Z :=
  match columns with
  | [::] => 0%Z
  | j :: remaining =>
      (putnam_1995_a6_entry M i j +
       putnam_1995_a6_sum_columns M i remaining)%Z
  end.

Definition putnam_1995_a6_row_sum {n : nat}
    (M : {ffun 'I_n -> 'I_6}) (i : 'I_3) : Z :=
  putnam_1995_a6_sum_columns M i (enum 'I_n).

Definition putnam_1995_a6_ordered_consecutive (a b c : Z) : bool :=
  Z.eqb b (a + 1)%Z && Z.eqb c (a + 2)%Z.

Definition putnam_1995_a6_consecutive {n : nat}
    (M : {ffun 'I_n -> 'I_6}) : bool :=
  let a := putnam_1995_a6_row_sum M (inord 0) in
  let b := putnam_1995_a6_row_sum M (inord 1) in
  let c := putnam_1995_a6_row_sum M (inord 2) in
  putnam_1995_a6_ordered_consecutive a b c ||
  putnam_1995_a6_ordered_consecutive a c b ||
  putnam_1995_a6_ordered_consecutive b a c ||
  putnam_1995_a6_ordered_consecutive b c a ||
  putnam_1995_a6_ordered_consecutive c a b ||
  putnam_1995_a6_ordered_consecutive c b a.

Definition putnam_1995_a6_equal {n : nat}
    (M : {ffun 'I_n -> 'I_6}) : bool :=
  [forall i : 'I_3,
    Z.eqb
      (putnam_1995_a6_row_sum M i)
      (putnam_1995_a6_row_sum M (inord 0))].

Theorem putnam_1995_a6 :
  exists n : nat,
    (1995 <= n)%nat /\
    (4 *
       #|[pred M : {ffun 'I_n -> 'I_6} |
           putnam_1995_a6_equal M]| <=
     #|[pred M : {ffun 'I_n -> 'I_6} |
         putnam_1995_a6_consecutive M]|)%nat.
Admitted.
