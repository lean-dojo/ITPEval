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
Require Import register_allocation_vcg.register_allocation.Spec.
Require Import register_allocation_vcg.register_allocation.DWP.
Open Scope Z_scope.
Axiom k : Z.
Axiom k'def : 2%Z ≤ k.
Program Fixpoint n (e : expr) : Z :=
match e with | Evar _ => 1%Z | Eneg e1 => n e1 | Eadd e1 e2 => (let n1 : Z := n e1 in let n2 : Z := n e2 in if decide (n1 = n2) then 1%Z + n1 else Z.max n1 n2) end.
Admit Obligations.
Program Fixpoint measure (e : expr) : Z :=
match e with | Evar _ => 0%Z | Eneg e1 => 1%Z + measure e1 | Eadd e1 e2 => 1%Z + (if decide (n e2 ≤ n e1) then measure e1 + measure e2 else 1%Z + measure e1 + measure e2) end.
Admit Obligations.
Axiom identity : (state -> bool) -> state -> bool.
Axiom exec_closure : instr -> state -> state.
Axiom identity_def : forall  (y : state -> bool), identity y = y.
Axiom exec_closure_def : forall  (y : instr) (y1 : state), exec_closure y y1 = exec y y1.
Theorem compile'vc (r : Z) (e : expr) (fact0 : 0%Z ≤ r) (fact1 : r < k) : let o1 : state -> state -> bool := expr_post e r in (match e with | Evar x => (∀(o2 : wcode), wcode_ok o2 ∧ trans1 o2 = identity -> wcode_ok o2) | Eneg e1 => (∀(o2 : wcode), wcode_ok o2 ∧ trans1 o2 = identity -> wcode_ok o2 ∧ (∀(o3 : wcode), wcode_ok o3 ∧ trans1 o3 = rcompose (trans1 o2) (rcompose (exec_closure (Ineg r))) -> ((0%Z ≤ measure e ∧ measure e1 < measure e) ∧ 0%Z ≤ r ∧ r < k) ∧ (∀(o4 : hcode), hcode_ok o4 ∧ post1 o4 = expr_post e1 r -> hcode_ok o4 ∧ (∀(o5 : wcode), wcode_ok o5 ∧ trans1 o5 = to_wp (post1 o4) -> wcode_ok o5 ∧ wcode_ok o3)))) | Eadd e1 e2 => (if decide (n e2 ≤ n e1) then if decide (r < k - 1%Z) then ∀(o2 : wcode), wcode_ok o2 ∧ trans1 o2 = identity -> wcode_ok o2 ∧ (∀(o3 : wcode), wcode_ok o3 ∧ trans1 o3 = rcompose (trans1 o2) (rcompose (exec_closure (Iadd (r + 1%Z) r))) -> (let o4 : Z := r + 1%Z in ((0%Z ≤ measure e ∧ measure e2 < measure e) ∧ 0%Z ≤ o4 ∧ o4 < k) ∧ (∀(o5 : hcode), hcode_ok o5 ∧ post1 o5 = expr_post e2 o4 -> hcode_ok o5 ∧ (∀(o6 : wcode), wcode_ok o6 ∧ trans1 o6 = to_wp (post1 o5) -> ((0%Z ≤ measure e ∧ measure e1 < measure e) ∧ 0%Z ≤ r ∧ r < k) ∧ (∀(o7 : hcode), hcode_ok o7 ∧ post1 o7 = expr_post e1 r -> hcode_ok o7 ∧ (∀(o8 : wcode), wcode_ok o8 ∧ trans1 o8 = to_wp (post1 o7) -> (wcode_ok o8 ∧ wcode_ok o6) ∧ (∀(o9 : wcode), wcode_ok o9 ∧ trans1 o9 = rcompose (trans1 o6) (trans1 o8) -> wcode_ok o9 ∧ wcode_ok o3))))))) else ∀(o2 : wcode), wcode_ok o2 ∧ trans1 o2 = identity -> wcode_ok o2 ∧ (∀(o3 : wcode), wcode_ok o3 ∧ trans1 o3 = rcompose (trans1 o2) (rcompose (exec_closure (Ipop (k - 2%Z)))) -> wcode_ok o3 ∧ (∀(o4 : wcode), wcode_ok o4 ∧ trans1 o4 = rcompose (trans1 o3) (rcompose (exec_closure (Iadd (k - 2%Z) (k - 1%Z)))) -> (let o5 : Z := k - 1%Z in ((0%Z ≤ measure e ∧ measure e2 < measure e) ∧ 0%Z ≤ o5 ∧ o5 < k) ∧ (∀(o6 : hcode), hcode_ok o6 ∧ post1 o6 = expr_post e2 o5 -> hcode_ok o6 ∧ (∀(o7 : wcode), wcode_ok o7 ∧ trans1 o7 = to_wp (post1 o6) -> (let o8 : Z := k - 2%Z in ((0%Z ≤ measure e ∧ measure e1 < measure e) ∧ 0%Z ≤ o8 ∧ o8 < k) ∧ (∀(o9 : hcode), hcode_ok o9 ∧ post1 o9 = expr_post e1 o8 -> hcode_ok o9 ∧ (∀(o10 : wcode), wcode_ok o10 ∧ trans1 o10 = to_wp (post1 o9) -> (wcode_ok o10 ∧ wcode_ok o7) ∧ (∀(o11 : wcode), wcode_ok o11 ∧ trans1 o11 = rcompose (trans1 o7) (trans1 o10) -> (wcode_ok o11 ∧ wcode_ok o4) ∧ (∀(o12 : wcode), wcode_ok o12 ∧ trans1 o12 = rcompose (trans1 o4) (trans1 o11) -> wcode_ok o12)))))))))) else let o2 : expr := Eadd e2 e1 in ((0%Z ≤ measure e ∧ measure o2 < measure e) ∧ 0%Z ≤ r ∧ r < k) ∧ (∀(o3 : hcode), hcode_ok o3 ∧ post1 o3 = expr_post o2 r -> hcode_ok o3)) end) ∧ (∀(o2 : wcode), (match e with | Evar x => (∃(o3 : wcode), (wcode_ok o3 ∧ trans1 o3 = identity) ∧ wcode_ok o2 ∧ trans1 o2 = rcompose (trans1 o3) (rcompose (exec_closure (Iload x r)))) | Eneg e1 => (∃(o3 : wcode), (wcode_ok o3 ∧ trans1 o3 = identity) ∧ (∃(o4 : wcode), (wcode_ok o4 ∧ trans1 o4 = rcompose (trans1 o3) (rcompose (exec_closure (Ineg r)))) ∧ (∃(o5 : hcode), (hcode_ok o5 ∧ post1 o5 = expr_post e1 r) ∧ (∃(o6 : wcode), (wcode_ok o6 ∧ trans1 o6 = to_wp (post1 o5)) ∧ wcode_ok o2 ∧ trans1 o2 = rcompose (trans1 o4) (trans1 o6))))) | Eadd e1 e2 => (if decide (n e2 ≤ n e1) then if decide (r < k - 1%Z) then ∃(o3 : wcode), (wcode_ok o3 ∧ trans1 o3 = identity) ∧ (∃(o4 : wcode), (wcode_ok o4 ∧ trans1 o4 = rcompose (trans1 o3) (rcompose (exec_closure (Iadd (r + 1%Z) r)))) ∧ (∃(o5 : hcode), (hcode_ok o5 ∧ post1 o5 = expr_post e2 (r + 1%Z)) ∧ (∃(o6 : wcode), (wcode_ok o6 ∧ trans1 o6 = to_wp (post1 o5)) ∧ (∃(o7 : hcode), (hcode_ok o7 ∧ post1 o7 = expr_post e1 r) ∧ (∃(o8 : wcode), (wcode_ok o8 ∧ trans1 o8 = to_wp (post1 o7)) ∧ (∃(o9 : wcode), (wcode_ok o9 ∧ trans1 o9 = rcompose (trans1 o6) (trans1 o8)) ∧ wcode_ok o2 ∧ trans1 o2 = rcompose (trans1 o4) (trans1 o9))))))) else ∃(o3 : wcode), (wcode_ok o3 ∧ trans1 o3 = identity) ∧ (∃(o4 : wcode), (wcode_ok o4 ∧ trans1 o4 = rcompose (trans1 o3) (rcompose (exec_closure (Ipop (k - 2%Z))))) ∧ (∃(o5 : wcode), (wcode_ok o5 ∧ trans1 o5 = rcompose (trans1 o4) (rcompose (exec_closure (Iadd (k - 2%Z) (k - 1%Z))))) ∧ (∃(o6 : hcode), (hcode_ok o6 ∧ post1 o6 = expr_post e2 (k - 1%Z)) ∧ (∃(o7 : wcode), (wcode_ok o7 ∧ trans1 o7 = to_wp (post1 o6)) ∧ (∃(o8 : hcode), (hcode_ok o8 ∧ post1 o8 = expr_post e1 (k - 2%Z)) ∧ (∃(o9 : wcode), (wcode_ok o9 ∧ trans1 o9 = to_wp (post1 o8)) ∧ (∃(o10 : wcode), (wcode_ok o10 ∧ trans1 o10 = rcompose (trans1 o7) (trans1 o9)) ∧ (∃(o11 : wcode), (wcode_ok o11 ∧ trans1 o11 = rcompose (trans1 o5) (trans1 o10)) ∧ wcode_ok o2 ∧ trans1 o2 = rcompose (trans1 o11) (rcompose (exec_closure (Ipush (k - 2%Z)))))))))))) else ∃(o3 : hcode), (hcode_ok o3 ∧ post1 o3 = expr_post (Eadd e2 e1) r) ∧ wcode_ok o2 ∧ trans1 o2 = to_wp (post1 o3)) end) -> (wcode_ok o2 ∧ (∀(x : state), trans1 o2 (o1 x) x = true)) ∧ (∀(result : hcode), hcode_ok result ∧ post1 result = o1 -> hcode_ok result ∧ post1 result = expr_post e r)).
Admitted.
