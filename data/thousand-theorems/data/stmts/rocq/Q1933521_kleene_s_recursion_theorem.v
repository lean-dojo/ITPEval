(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1933521
  (thousand-theorems__rocq__Q1933521), "Kleene's recursion theorem": every
  binary partial-recursive operation on a program code and a natural input has
  a code whose partial evaluation is extensionally the operation applied to
  that same code. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat Arith.Peano_dec.

Module Q1933521_Kleene_Recursion.

Definition q1933521_nat_pair (a b : nat) : nat :=
  if Nat.ltb a b then b * b + a else a * a + a + b.

Definition q1933521_nat_unpair (n : nat) : nat * nat :=
  let s := Nat.sqrt n in
  if Nat.ltb (n - s * s) s
  then (n - s * s, s)
  else (s, n - s * s - s).

Inductive q1933521_code : Type :=
| Q1933521_Code_zero : q1933521_code
| Q1933521_Code_succ : q1933521_code
| Q1933521_Code_left : q1933521_code
| Q1933521_Code_right : q1933521_code
| Q1933521_Code_pair :
    q1933521_code -> q1933521_code -> q1933521_code
| Q1933521_Code_comp :
    q1933521_code -> q1933521_code -> q1933521_code
| Q1933521_Code_prec :
    q1933521_code -> q1933521_code -> q1933521_code
| Q1933521_Code_rfind :
    q1933521_code -> q1933521_code.

Fixpoint q1933521_code_encode (c : q1933521_code) : nat :=
  match c with
  | Q1933521_Code_zero => 0
  | Q1933521_Code_succ => 1
  | Q1933521_Code_left => 2
  | Q1933521_Code_right => 3
  | Q1933521_Code_pair cf cg =>
      2 * (2 * q1933521_nat_pair
        (q1933521_code_encode cf)
        (q1933521_code_encode cg)) + 4
  | Q1933521_Code_comp cf cg =>
      2 * (2 * q1933521_nat_pair
        (q1933521_code_encode cf)
        (q1933521_code_encode cg) + 1) + 4
  | Q1933521_Code_prec cf cg =>
      2 * (2 * q1933521_nat_pair
        (q1933521_code_encode cf)
        (q1933521_code_encode cg)) + 1 + 4
  | Q1933521_Code_rfind cf =>
      2 * (2 * q1933521_code_encode cf + 1) + 1 + 4
  end.

Inductive q1933521_evaluates :
    q1933521_code -> nat -> nat -> Prop :=
| Q1933521_Eval_zero :
    forall input,
      q1933521_evaluates Q1933521_Code_zero input 0
| Q1933521_Eval_succ :
    forall input,
      q1933521_evaluates Q1933521_Code_succ input (S input)
| Q1933521_Eval_left :
    forall input,
      q1933521_evaluates Q1933521_Code_left input
        (fst (q1933521_nat_unpair input))
| Q1933521_Eval_right :
    forall input,
      q1933521_evaluates Q1933521_Code_right input
        (snd (q1933521_nat_unpair input))
| Q1933521_Eval_pair :
    forall cf cg input left_value right_value,
      q1933521_evaluates cf input left_value ->
      q1933521_evaluates cg input right_value ->
      q1933521_evaluates (Q1933521_Code_pair cf cg) input
        (q1933521_nat_pair left_value right_value)
| Q1933521_Eval_comp :
    forall cf cg input middle output,
      q1933521_evaluates cg input middle ->
      q1933521_evaluates cf middle output ->
      q1933521_evaluates (Q1933521_Code_comp cf cg) input output
| Q1933521_Eval_prec_zero :
    forall cf cg parameter output,
      q1933521_evaluates cf parameter output ->
      q1933521_evaluates (Q1933521_Code_prec cf cg)
        (q1933521_nat_pair parameter 0) output
| Q1933521_Eval_prec_succ :
    forall cf cg parameter index previous output,
      q1933521_evaluates (Q1933521_Code_prec cf cg)
        (q1933521_nat_pair parameter index) previous ->
      q1933521_evaluates cg
        (q1933521_nat_pair parameter
          (q1933521_nat_pair index previous)) output ->
      q1933521_evaluates (Q1933521_Code_prec cf cg)
        (q1933521_nat_pair parameter (S index)) output
| Q1933521_Eval_rfind :
    forall cf parameter start offset,
      q1933521_evaluates cf
        (q1933521_nat_pair parameter (offset + start)) 0 ->
      (forall i,
        (i < offset)%nat ->
        exists value,
          q1933521_evaluates cf
            (q1933521_nat_pair parameter (i + start)) value /\
          value <> 0) ->
      q1933521_evaluates (Q1933521_Code_rfind cf)
        (q1933521_nat_pair parameter start) (offset + start).

Record q1933521_partial_function : Type := {
  q1933521_graph : nat -> nat -> Prop;
  q1933521_graph_functional :
    forall input first second,
      q1933521_graph input first ->
      q1933521_graph input second ->
      first = second
}.

Arguments q1933521_graph _ _ _.

Definition q1933521_partrec2
    (f : q1933521_code -> q1933521_partial_function) : Prop :=
  exists program : q1933521_code,
    forall (c : q1933521_code) (input output : nat),
      q1933521_evaluates program
        (q1933521_nat_pair (q1933521_code_encode c) input) output <->
      q1933521_graph (f c) input output.

Theorem q1933521_kleene_second_recursion :
  forall f : q1933521_code -> q1933521_partial_function,
    q1933521_partrec2 f ->
    exists c : q1933521_code,
      forall input output : nat,
        q1933521_evaluates c input output <->
        q1933521_graph (f c) input output.
Proof.
Admitted.

End Q1933521_Kleene_Recursion.
