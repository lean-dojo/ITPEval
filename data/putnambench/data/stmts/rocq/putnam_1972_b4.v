(* Statement-only formalization of PutnamBench artifact putnam_1972_b4:
   an integer-coefficient polynomial in three variables recovers x from
   x^n, x^(n+1), and x + x^(n+2). This file contains no proof. *)

From Stdlib Require Import ZArith List.

Open Scope Z_scope.

Fixpoint zpow_nat (x : Z) (n : nat) : Z :=
  match n with
  | O => 1
  | S k => x * zpow_nat x k
  end.

Fixpoint eval_int_poly (P : list Z) (x : Z) : Z :=
  match P with
  | nil => 0
  | coefficient :: rest =>
      coefficient + x * eval_int_poly rest x
  end.

Fixpoint eval_int_poly2
    (P : list (list Z)) (a b : Z) : Z :=
  match P with
  | nil => 0
  | coefficient :: rest =>
      eval_int_poly coefficient a +
      b * eval_int_poly2 rest a b
  end.

Fixpoint eval_int_poly3
    (P : list (list (list Z))) (a b c : Z) : Z :=
  match P with
  | nil => 0
  | coefficient :: rest =>
      eval_int_poly2 coefficient a b +
      c * eval_int_poly3 rest a b c
  end.

Theorem putnam_1972_b4
    (n : nat)
    (hn : (n > 1)%nat) :
  exists P : list (list (list Z)),
    forall x : Z,
      x = eval_int_poly3 P
        (zpow_nat x n)
        (zpow_nat x (n + 1)%nat)
        (x + zpow_nat x (n + 2)%nat).
Admitted.
