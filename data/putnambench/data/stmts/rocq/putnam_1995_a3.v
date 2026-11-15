(* Statement-only formalization of PutnamBench artifact putnam_1995_a3:
   divisibility by seven after successive coordinatewise replacements in
   nine-digit decimal numbers forces corresponding outer digits to be
   congruent modulo seven. This file contains no proof. *)

From Stdlib Require Import ZArith Vectors.Fin.

Open Scope Z_scope.

Definition putnam_1995_a3_digits : Type :=
  Fin.t 9 -> Z.

Fixpoint putnam_1995_a3_fin_sum
    (n : nat) : (Fin.t n -> Z) -> Z :=
  match n as k return (Fin.t k -> Z) -> Z with
  | O => fun _ => 0
  | S k =>
      fun u =>
        u Fin.F1 +
        putnam_1995_a3_fin_sum k (fun i => u (Fin.FS i))
  end.

Definition putnam_1995_a3_index_value
    {n : nat} (i : Fin.t n) : nat :=
  proj1_sig (Fin.to_nat i).

Definition putnam_1995_a3_decimal_value
    (digits : putnam_1995_a3_digits) : Z :=
  putnam_1995_a3_fin_sum 9
    (fun i =>
      digits i *
      Z.pow 10 (Z.of_nat (putnam_1995_a3_index_value i))).

Theorem putnam_1995_a3
    (relation :
      putnam_1995_a3_digits ->
      putnam_1995_a3_digits ->
      Prop)
    (digits_to_num : putnam_1995_a3_digits -> Z)
    (hdigits_to_num :
      digits_to_num = putnam_1995_a3_decimal_value)
    (hrelation :
      forall d e : putnam_1995_a3_digits,
        relation d e <->
        (forall i : Fin.t 9,
          0 <= d i < 10 /\
          0 <= e i < 10) /\
        (forall i : Fin.t 9,
          Z.divide 7
            (digits_to_num
              (fun j : Fin.t 9 =>
                if Fin.eq_dec j i then e j else d j)))) :
  forall d e f : putnam_1995_a3_digits,
    relation d e /\
    relation e f ->
    forall i : Fin.t 9,
      Z.divide 7 (d i - f i).
Admitted.
