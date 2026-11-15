From Stdlib Require Import Strings.String.
From Stdlib Require Import String Ascii.
From Stdlib Require Arith.
From stdpp Require Import base.
From stdpp Require Import fin_maps.
From stdpp Require Import gmap.
From stdpp Require Import base gmultiset.
From Stdlib Require Classical.
From Stdlib Require Import ZArith.
From stdpp.bitvector Require Import definitions tactics.
From Stdlib Require Import Sorting.Sorted.
From Stdlib Require Import Reals.Rbasic_fun.
From Stdlib Require Import Reals.Abstract.ConstructiveAbs.
From Stdlib Require Import Reals.Rdefinitions.
From stdpp Require Import list_relations.
From stdpp Require Import list_numbers.
From stdpp Require Import functions.
From Stdlib Require Import ClassicalEpsilon.
From stdpp Require Import base decidable.
From Stdlib Require Import ZArith.Zeuclid.
From Stdlib Require Import ZArith.Znumtheory.
From stdpp Require Import propset.
From Stdlib Require Import Reals.
Require Import Why3.Base.
Require Import defunctionalization_vcg.defunctionalization.Expr.
Require Import defunctionalization_vcg.defunctionalization.DirectSem.
Require Import defunctionalization_vcg.defunctionalization.Defunctionalization.
Open Scope Z_scope.
Inductive value :=
  | Vnum : Z -> value
  | Underflow : value.
Axiom value_inhabited : Inhabited value.
Global Existing Instance value_inhabited.
Axiom value_countable : Countable value.
Global Existing Instance value_countable.
Program Fixpoint eval_0 (e : expr) : value :=
match e with | Cte n => (if decide (0%Z ≤ n) then Vnum n else Underflow) | Sub e1 e2 => (match eval_0 e1 with | Underflow => Underflow | Vnum v1 => (match eval_0 e2 with | Underflow => Underflow | Vnum v2 => (if decide (v2 ≤ v1) then Vnum (v1 - v2) else Underflow) end) end) end.
Admit Obligations.
Axiom fc : forall {α : Type} `{Inhabited α}, (value -> α) -> Z -> value -> α.
Axiom fc1 : forall {α : Type} `{Inhabited α}, (value -> α) -> expr -> value -> α.
Axiom fc'def : forall  {α : Type} `{Inhabited α} (k : value -> α) (v1 : Z) (v2 : value), fc k v1 v2 = (match v2 with | Underflow => k Underflow | Vnum v21 => k (if decide (v21 ≤ v1) then Vnum (v1 - v21) else Underflow) end).
Program Fixpoint eval_1 {α : Type} `{Inhabited α} (e : expr) (k : value -> α) : α :=
match e with | Cte n => k (if decide (0%Z ≤ n) then Vnum n else Underflow) | Sub e1 e2 => eval_1 e1 (fc1 k e2) end.
Admit Obligations.
Axiom fc'def1 : forall  {α : Type} `{Inhabited α} (k : value -> α) (e2 : expr) (v1 : value), fc1 k e2 v1 = (match v1 with | Underflow => k Underflow | Vnum v11 => eval_1 e2 (fc k v11) end).
Axiom identity : value -> value.
Axiom identity_def : forall  (y : value), identity y = y.
Definition interpret_1 (p : expr) : value := eval_1 p identity.
Axiom eval_2a : forall {α : Type} `{Inhabited α}, expr -> (Z -> α) -> (unit -> α) -> Z -> α.
Axiom eval_2b : forall {α : Type} `{Inhabited α}, Z -> (Z -> α) -> (unit -> α) -> Z -> α.
Axiom eval_2b'def : forall  {α : Type} `{Inhabited α} (v1 : Z) (k : Z -> α) (kerr : unit -> α) (v2 : Z), eval_2b v1 k kerr v2 = (if decide (v2 ≤ v1) then k (v1 - v2) else kerr ()).
Program Fixpoint eval_2 {α : Type} `{Inhabited α} (e : expr) (k : Z -> α) (kerr : unit -> α) : α :=
match e with | Cte n => (if decide (0%Z ≤ n) then k n else kerr ()) | Sub e1 e2 => eval_2 e1 (eval_2a e2 k kerr) kerr end.
Admit Obligations.
Axiom eval_2a'def : forall  {α : Type} `{Inhabited α} (e2 : expr) (k : Z -> α) (kerr : unit -> α) (v1 : Z), eval_2a e2 k kerr v1 = eval_2 e2 (eval_2b v1 k kerr) kerr.
Axiom Vnum_closure : Z -> value.
Axiom fc2 : unit -> value.
Axiom Vnum_closure_def : forall  (y : Z), Vnum_closure y = Vnum y.
Axiom fc'def2 : forall  (x : unit), fc2 x = Underflow.
Definition interpret_2 (p : expr) : value := eval_2 p Vnum_closure fc2.
Axiom eval_3a : expr -> (Z -> value) -> Z -> value.
Axiom eval_3b : Z -> (Z -> value) -> Z -> value.
Axiom eval_3b'def : forall  (v1 : Z) (k : Z -> value) (v2 : Z), eval_3b v1 k v2 = (if decide (v2 ≤ v1) then k (v1 - v2) else Underflow).
Program Fixpoint eval_3 (e : expr) (k : Z -> value) : value :=
match e with | Cte n => (if decide (0%Z ≤ n) then k n else Underflow) | Sub e1 e2 => eval_3 e1 (eval_3a e2 k) end.
Admit Obligations.
Axiom eval_3a'def : forall  (e2 : expr) (k : Z -> value) (v1 : Z), eval_3a e2 k v1 = eval_3 e2 (eval_3b v1 k).
Definition interpret_3 (p : expr) : value := eval_3 p Vnum_closure.
Inductive cont :=
  | I : cont
  | A : expr -> cont -> cont
  | B : Z -> cont -> cont.
Axiom cont_inhabited : Inhabited cont.
Global Existing Instance cont_inhabited.
Axiom cont_countable : Countable cont.
Global Existing Instance cont_countable.
Inductive eval_cont : cont -> value -> value -> Prop :=
 | underflow (k : cont) : eval_cont k Underflow Underflow
 | a1 (v : Z) (k : cont) (e2 : expr) (r : value) : eval_cont (B v k) (eval_0 e2) r -> eval_cont (A e2 k) (Vnum v) r
 | a2 (k : cont) (v : Z) (v1 : Z) (r : value) : eval_cont k (if decide (v ≤ v1) then Vnum (v1 - v) else Underflow) r -> eval_cont (B v1 k) (Vnum v) r
 | a3 (v : Z) : eval_cont I (Vnum v) (Vnum v).
Program Fixpoint size_e (e : expr) : Z :=
match e with | Cte _ => 1%Z | Sub e1 e2 => 3%Z + size_e e1 + size_e e2 end.
Admit Obligations.
Program Fixpoint size_c (c : cont) : Z :=
match c with | I => 0%Z | A e2 k => 2%Z + Defunctionalization.size_e e2 + size_c k | B _ k => 1%Z + size_c k end.
Admit Obligations.
Theorem eval_4'vc (e : expr) (c : cont) : (match e with | Cte n => 0%Z ≤ n -> (0%Z ≤ size_c c + Defunctionalization.size_e e ∧ size_c c < size_c c + Defunctionalization.size_e e) ∧ 0%Z ≤ n | Sub e1 e2 => 0%Z ≤ size_c c + Defunctionalization.size_e e ∧ size_c (A e2 c) + Defunctionalization.size_e e1 < size_c c + Defunctionalization.size_e e end) ∧ (∀(result : value), (match e with | Cte n => (if decide (0%Z ≤ n) then eval_cont c (Vnum n) result else result = Underflow) | Sub e1 e2 => eval_cont (A e2 c) (eval_0 e1) result end) -> eval_cont c (eval_0 e) result).
Admitted.
