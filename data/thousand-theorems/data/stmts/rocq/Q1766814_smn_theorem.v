(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1766814
  (thousand-theorems__rocq__Q1766814), "Smn theorem": a total computable
  specialization function fixes the first natural-number input of a coded
  partial recursive program. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat Arith.Peano_dec.

Module Q1766814_Smn.

Definition nat_pair (a b : nat) : nat :=
  if Nat.ltb a b then b * b + a else a * a + a + b.

Definition nat_unpair (n : nat) : nat * nat :=
  let s := Nat.sqrt n in
  if Nat.ltb (n - s * s) s
  then (n - s * s, s)
  else (s, n - s * s - s).

Inductive code : Type :=
| Code_zero : code
| Code_succ : code
| Code_left : code
| Code_right : code
| Code_pair : code -> code -> code
| Code_comp : code -> code -> code
| Code_prec : code -> code -> code
| Code_rfind : code -> code.

Fixpoint code_encode (c : code) : nat :=
  match c with
  | Code_zero => 0
  | Code_succ => 1
  | Code_left => 2
  | Code_right => 3
  | Code_pair cf cg =>
      2 * (2 * nat_pair (code_encode cf) (code_encode cg)) + 4
  | Code_comp cf cg =>
      2 * (2 * nat_pair (code_encode cf) (code_encode cg) + 1) + 4
  | Code_prec cf cg =>
      2 * (2 * nat_pair (code_encode cf) (code_encode cg)) + 1 + 4
  | Code_rfind cf =>
      2 * (2 * code_encode cf + 1) + 1 + 4
  end.

Inductive evaluates : code -> nat -> nat -> Prop :=
| Eval_zero :
    forall input,
      evaluates Code_zero input 0
| Eval_succ :
    forall input,
      evaluates Code_succ input (S input)
| Eval_left :
    forall input,
      evaluates Code_left input (fst (nat_unpair input))
| Eval_right :
    forall input,
      evaluates Code_right input (snd (nat_unpair input))
| Eval_pair :
    forall cf cg input left_value right_value,
      evaluates cf input left_value ->
      evaluates cg input right_value ->
      evaluates (Code_pair cf cg) input
        (nat_pair left_value right_value)
| Eval_comp :
    forall cf cg input middle output,
      evaluates cg input middle ->
      evaluates cf middle output ->
      evaluates (Code_comp cf cg) input output
| Eval_prec_zero :
    forall cf cg parameter output,
      evaluates cf parameter output ->
      evaluates (Code_prec cf cg) (nat_pair parameter 0) output
| Eval_prec_succ :
    forall cf cg parameter index previous output,
      evaluates (Code_prec cf cg) (nat_pair parameter index) previous ->
      evaluates cg
        (nat_pair parameter (nat_pair index previous)) output ->
      evaluates (Code_prec cf cg)
        (nat_pair parameter (S index)) output
| Eval_rfind :
    forall cf parameter start offset,
      evaluates cf (nat_pair parameter (offset + start)) 0 ->
      (forall i,
        (i < offset)%nat ->
        exists value,
          evaluates cf (nat_pair parameter (i + start)) value /\
          value <> 0) ->
      evaluates (Code_rfind cf) (nat_pair parameter start)
        (offset + start).

Definition computable2 (f : code -> nat -> code) : Prop :=
  exists program : code,
    forall (c : code) (n output : nat),
      evaluates program (nat_pair (code_encode c) n) output <->
      output = code_encode (f c n).

Theorem q1766814_smn :
  exists f : code -> nat -> code,
    computable2 f /\
    forall (c : code) (n x output : nat),
      evaluates (f c n) x output <->
      evaluates c (nat_pair n x) output.
Admitted.

End Q1766814_Smn.
