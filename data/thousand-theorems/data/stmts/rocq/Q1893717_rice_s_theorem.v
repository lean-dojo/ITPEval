(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1893717
  (thousand-theorems__rocq__Q1893717), "Rice's theorem": every computably
  decidable extensional property of partial-recursive natural-number functions
  that holds for one such function holds for all of them. This file contains
  no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Module Q1893717_Rice.

(* The square pairing used by the source Nat.Partrec development. *)
Definition q1893717_nat_pair (a b : nat) : nat :=
  if Nat.ltb a b then b * b + a else a * a + a + b.

(* Codes for a universal system of partial-recursive unary functions. *)
Inductive q1893717_code : Type :=
| Q1893717_Code_zero : q1893717_code
| Q1893717_Code_succ : q1893717_code
| Q1893717_Code_left : q1893717_code
| Q1893717_Code_right : q1893717_code
| Q1893717_Code_pair :
    q1893717_code -> q1893717_code -> q1893717_code
| Q1893717_Code_comp :
    q1893717_code -> q1893717_code -> q1893717_code
| Q1893717_Code_prec :
    q1893717_code -> q1893717_code -> q1893717_code
| Q1893717_Code_rfind :
    q1893717_code -> q1893717_code.

(* A computable numerical encoding of program codes. *)
Fixpoint q1893717_code_encode (c : q1893717_code) : nat :=
  match c with
  | Q1893717_Code_zero => 0
  | Q1893717_Code_succ => 1
  | Q1893717_Code_left => 2
  | Q1893717_Code_right => 3
  | Q1893717_Code_pair cf cg =>
      4 * q1893717_nat_pair
        (q1893717_code_encode cf) (q1893717_code_encode cg) + 4
  | Q1893717_Code_comp cf cg =>
      4 * q1893717_nat_pair
        (q1893717_code_encode cf) (q1893717_code_encode cg) + 6
  | Q1893717_Code_prec cf cg =>
      4 * q1893717_nat_pair
        (q1893717_code_encode cf) (q1893717_code_encode cg) + 5
  | Q1893717_Code_rfind cf =>
      4 * q1893717_code_encode cf + 7
  end.

(* Relational evaluation means that the coded computation terminates with
   the displayed output. *)
Inductive q1893717_evaluates :
    q1893717_code -> nat -> nat -> Prop :=
| Q1893717_Eval_zero :
    forall input,
      q1893717_evaluates Q1893717_Code_zero input 0
| Q1893717_Eval_succ :
    forall input,
      q1893717_evaluates Q1893717_Code_succ input (S input)
| Q1893717_Eval_left :
    forall left right,
      q1893717_evaluates Q1893717_Code_left
        (q1893717_nat_pair left right) left
| Q1893717_Eval_right :
    forall left right,
      q1893717_evaluates Q1893717_Code_right
        (q1893717_nat_pair left right) right
| Q1893717_Eval_pair :
    forall cf cg input left_value right_value,
      q1893717_evaluates cf input left_value ->
      q1893717_evaluates cg input right_value ->
      q1893717_evaluates (Q1893717_Code_pair cf cg) input
        (q1893717_nat_pair left_value right_value)
| Q1893717_Eval_comp :
    forall cf cg input middle output,
      q1893717_evaluates cg input middle ->
      q1893717_evaluates cf middle output ->
      q1893717_evaluates (Q1893717_Code_comp cf cg) input output
| Q1893717_Eval_prec_zero :
    forall cf cg parameter output,
      q1893717_evaluates cf parameter output ->
      q1893717_evaluates (Q1893717_Code_prec cf cg)
        (q1893717_nat_pair parameter 0) output
| Q1893717_Eval_prec_succ :
    forall cf cg parameter index previous output,
      q1893717_evaluates (Q1893717_Code_prec cf cg)
        (q1893717_nat_pair parameter index) previous ->
      q1893717_evaluates cg
        (q1893717_nat_pair parameter
          (q1893717_nat_pair index previous)) output ->
      q1893717_evaluates (Q1893717_Code_prec cf cg)
        (q1893717_nat_pair parameter (S index)) output
| Q1893717_Eval_rfind_zero :
    forall cf parameter start,
      q1893717_evaluates cf
        (q1893717_nat_pair parameter start) 0 ->
      q1893717_evaluates (Q1893717_Code_rfind cf)
        (q1893717_nat_pair parameter start) start
| Q1893717_Eval_rfind_succ :
    forall cf parameter start nonzero_value output,
      q1893717_evaluates cf
        (q1893717_nat_pair parameter start) (S nonzero_value) ->
      q1893717_evaluates (Q1893717_Code_rfind cf)
        (q1893717_nat_pair parameter (S start)) output ->
      q1893717_evaluates (Q1893717_Code_rfind cf)
        (q1893717_nat_pair parameter start) output.

(* Partial functions are represented extensionally by their termination
   graphs. Program denotations are functional by the deterministic clauses
   above. *)
Definition q1893717_partial_function : Type :=
  nat -> nat -> Prop.

Definition q1893717_evaluate
    (c : q1893717_code) : q1893717_partial_function :=
  fun input output => q1893717_evaluates c input output.

Definition q1893717_same_partial_function
    (f g : q1893717_partial_function) : Prop :=
  forall input output, f input output <-> g input output.

Definition q1893717_partial_recursive
    (f : q1893717_partial_function) : Prop :=
  exists c : q1893717_code,
    q1893717_same_partial_function f (q1893717_evaluate c).

(* This record represents a set of partial functions independently of the
   chosen graph presentation. *)
Record q1893717_partial_property : Type := {
  q1893717_holds : q1893717_partial_function -> Prop;
  q1893717_holds_extensional :
    forall f g,
      q1893717_same_partial_function f g ->
      (q1893717_holds f <-> q1893717_holds g)
}.

(* A predicate on codes is computable when a coded program computes its
   total Boolean characteristic function. *)
Definition q1893717_computable_predicate
    (P : q1893717_code -> Prop) : Prop :=
  exists decision : q1893717_code -> bool,
    (forall c, decision c = true <-> P c) /\
    exists program : q1893717_code,
      forall c output,
        q1893717_evaluates program
          (q1893717_code_encode c) output <->
        output = (if decision c then 1 else 0).

Theorem q1893717_rice :
  forall C : q1893717_partial_property,
    q1893717_computable_predicate
      (fun c => q1893717_holds C (q1893717_evaluate c)) ->
    forall f g : q1893717_partial_function,
      q1893717_partial_recursive f ->
      q1893717_partial_recursive g ->
      q1893717_holds C f ->
      q1893717_holds C g.
Admitted.

End Q1893717_Rice.
