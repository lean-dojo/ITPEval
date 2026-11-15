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
Require Import imp.imp.Syntax.
Require Import imp.imp.ConcreteSemantics.
Require Import imp.dict.Imperative.
Open Scope Z_scope.
Axiom env : Type.
Axiom env_inhabited : Inhabited env.
Global Existing Instance env_inhabited.
Axiom env_countable : Countable env.
Global Existing Instance env_countable.
Theorem interp_expr'vc (e : expr) (env1 : t program_var Z) : match e with | Elit n => eval_expr (model1 env1) e (Enormal n) | Evar x => (∀(result : Z), (match get env1 x with | None => False | Some v => result = v end) -> eval_expr (model1 env1) e (Enormal result)) ∧ (get env1 x = None -> eval_expr (model1 env1) e Eunbound_var) | Esub e1 e2 => (match e with | Elit _ => False | Evar _ => False | Esub f f1 => f = e2 ∨ f1 = e2 end) ∧ (∀(o1 : Z), eval_expr (model1 env1) e2 (Enormal o1) -> (match e with | Elit _ => False | Evar _ => False | Esub f f1 => f = e1 ∨ f1 = e1 end) ∧ (∀(o2 : Z), eval_expr (model1 env1) e1 (Enormal o2) -> eval_expr (model1 env1) e (Enormal (o2 - o1))) ∧ (eval_expr (model1 env1) e1 Eunbound_var -> eval_expr (model1 env1) e Eunbound_var)) ∧ (eval_expr (model1 env1) e2 Eunbound_var -> eval_expr (model1 env1) e Eunbound_var) end.
Admitted.
