(*
  Statement-only formalization of Logipedia corpus artifact
  cong.let_clause_1034 (catalog title "cong.let_clause_1034"):
  the natural-number quotient-remainder reconstruction identity, including
  the source operations' behavior at a zero divisor. This file contains no
  proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition cong_source_div (n d : nat) : nat :=
  match d with
  | O => S n
  | S d' => Nat.div n (S d')
  end.

Definition cong_source_mod (n d : nat) : nat :=
  match d with
  | O => n
  | S d' => Nat.modulo n (S d')
  end.

Theorem cong_let_clause_1034 :
  forall n m p : nat,
    0 < p ->
    forall x2515 x2516 : nat,
      x2515 =
      cong_source_mod x2515 x2516 +
      x2516 * cong_source_div x2515 x2516.
Admitted.
