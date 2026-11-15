(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3007384
  (thousand-theorems__rocq__Q3007384), "Post's theorem": on an arbitrary
  primitively codable type, a decidable predicate is computable exactly when
  it and its complement are recursively enumerable. This file contains no
  proof.
*)

From Stdlib Require Import Arith.PeanoNat Arith.Peano_dec.

Module Q3007384_Post.

Definition q3007384_nat_pair (a b : nat) : nat :=
  if Nat.ltb a b then b * b + a else a * a + a + b.

Definition q3007384_nat_unpair (n : nat) : nat * nat :=
  let s := Nat.sqrt n in
  if Nat.ltb (n - s * s) s
  then (n - s * s, s)
  else (s, n - s * s - s).

Inductive q3007384_code : Type :=
| Q3007384_Code_zero : q3007384_code
| Q3007384_Code_succ : q3007384_code
| Q3007384_Code_left : q3007384_code
| Q3007384_Code_right : q3007384_code
| Q3007384_Code_pair :
    q3007384_code -> q3007384_code -> q3007384_code
| Q3007384_Code_comp :
    q3007384_code -> q3007384_code -> q3007384_code
| Q3007384_Code_prec :
    q3007384_code -> q3007384_code -> q3007384_code
| Q3007384_Code_rfind :
    q3007384_code -> q3007384_code.

Inductive q3007384_primitive_recursive_code :
    q3007384_code -> Prop :=
| Q3007384_PR_zero :
    q3007384_primitive_recursive_code Q3007384_Code_zero
| Q3007384_PR_succ :
    q3007384_primitive_recursive_code Q3007384_Code_succ
| Q3007384_PR_left :
    q3007384_primitive_recursive_code Q3007384_Code_left
| Q3007384_PR_right :
    q3007384_primitive_recursive_code Q3007384_Code_right
| Q3007384_PR_pair :
    forall cf cg,
      q3007384_primitive_recursive_code cf ->
      q3007384_primitive_recursive_code cg ->
      q3007384_primitive_recursive_code
        (Q3007384_Code_pair cf cg)
| Q3007384_PR_comp :
    forall cf cg,
      q3007384_primitive_recursive_code cf ->
      q3007384_primitive_recursive_code cg ->
      q3007384_primitive_recursive_code
        (Q3007384_Code_comp cf cg)
| Q3007384_PR_prec :
    forall cf cg,
      q3007384_primitive_recursive_code cf ->
      q3007384_primitive_recursive_code cg ->
      q3007384_primitive_recursive_code
        (Q3007384_Code_prec cf cg).

Inductive q3007384_evaluates :
    q3007384_code -> nat -> nat -> Prop :=
| Q3007384_Eval_zero :
    forall input,
      q3007384_evaluates Q3007384_Code_zero input 0
| Q3007384_Eval_succ :
    forall input,
      q3007384_evaluates Q3007384_Code_succ input (S input)
| Q3007384_Eval_left :
    forall input,
      q3007384_evaluates Q3007384_Code_left input
        (fst (q3007384_nat_unpair input))
| Q3007384_Eval_right :
    forall input,
      q3007384_evaluates Q3007384_Code_right input
        (snd (q3007384_nat_unpair input))
| Q3007384_Eval_pair :
    forall cf cg input left_value right_value,
      q3007384_evaluates cf input left_value ->
      q3007384_evaluates cg input right_value ->
      q3007384_evaluates (Q3007384_Code_pair cf cg) input
        (q3007384_nat_pair left_value right_value)
| Q3007384_Eval_comp :
    forall cf cg input middle output,
      q3007384_evaluates cg input middle ->
      q3007384_evaluates cf middle output ->
      q3007384_evaluates (Q3007384_Code_comp cf cg) input output
| Q3007384_Eval_prec_zero :
    forall cf cg parameter output,
      q3007384_evaluates cf parameter output ->
      q3007384_evaluates (Q3007384_Code_prec cf cg)
        (q3007384_nat_pair parameter 0) output
| Q3007384_Eval_prec_succ :
    forall cf cg parameter index previous output,
      q3007384_evaluates (Q3007384_Code_prec cf cg)
        (q3007384_nat_pair parameter index) previous ->
      q3007384_evaluates cg
        (q3007384_nat_pair parameter
          (q3007384_nat_pair index previous)) output ->
      q3007384_evaluates (Q3007384_Code_prec cf cg)
        (q3007384_nat_pair parameter (S index)) output
| Q3007384_Eval_rfind :
    forall cf parameter start offset,
      q3007384_evaluates cf
        (q3007384_nat_pair parameter (offset + start)) 0 ->
      (forall i,
        (i < offset)%nat ->
        exists value,
          q3007384_evaluates cf
            (q3007384_nat_pair parameter (i + start)) value /\
          value <> 0) ->
      q3007384_evaluates (Q3007384_Code_rfind cf)
        (q3007384_nat_pair parameter start) (offset + start).

Definition q3007384_option_encode
    {A : Type}
    (encode : A -> nat)
    (value : option A) : nat :=
  match value with
  | None => 0
  | Some a => S (encode a)
  end.

Record q3007384_primcodable (A : Type) : Type := {
  q3007384_encode : A -> nat;
  q3007384_decode : nat -> option A;
  q3007384_decode_encode :
    forall a,
      q3007384_decode (q3007384_encode a) = Some a;
  q3007384_decode_program : q3007384_code;
  q3007384_decode_program_primitive :
    q3007384_primitive_recursive_code q3007384_decode_program;
  q3007384_decode_computable :
    forall input output,
      q3007384_evaluates q3007384_decode_program input output <->
      output =
        q3007384_option_encode q3007384_encode
          (q3007384_decode input)
}.

Arguments q3007384_encode {A} _ _.
Arguments q3007384_decode {A} _ _.

Definition q3007384_computable_predicate
    {A : Type}
    (coding : q3007384_primcodable A)
    (p : A -> Prop) : Prop :=
  exists decision : A -> bool,
    (forall a, decision a = true <-> p a) /\
    exists program : q3007384_code,
      forall a output,
        q3007384_evaluates program
          (q3007384_encode coding a) output <->
        output = if decision a then 1 else 0.

Definition q3007384_recursively_enumerable
    {A : Type}
    (coding : q3007384_primcodable A)
    (p : A -> Prop) : Prop :=
  exists program : q3007384_code,
    forall a,
      p a <->
      exists output,
        q3007384_evaluates program
          (q3007384_encode coding a) output.

Theorem q3007384_post :
  forall
    (A : Type)
    (coding : q3007384_primcodable A)
    (p : A -> Prop),
    (forall a, {p a} + {~ p a}) ->
    q3007384_computable_predicate coding p <->
    q3007384_recursively_enumerable coding p /\
    q3007384_recursively_enumerable coding (fun a => ~ p a).
Admitted.

End Q3007384_Post.
