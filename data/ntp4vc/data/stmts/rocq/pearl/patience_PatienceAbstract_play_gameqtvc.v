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
Require Import Why3.why3.Ref.Ref.
Require Import Why3.map.Const.
Require Import patience_vcg.patience.PigeonHole.
Open Scope Z_scope.
Axiom card : Type.
Axiom card_inhabited : Inhabited card.
Global Existing Instance card_inhabited.
Axiom card_countable : Countable card.
Global Existing Instance card_countable.
Inductive state :=
  | state'mk : Z -> Z -> (Z -> Z) -> (Z -> Z) -> (Z -> Z -> Z) -> (Z -> Z * Z) -> (Z -> Z) -> state.
Axiom state_inhabited : Inhabited state.
Global Existing Instance state_inhabited.
Axiom state_countable : Countable state.
Global Existing Instance state_countable.
Definition num_stacks (x : state) := match x with |  state'mk a _ _ _ _ _ _ => a end.
Definition num_elts (x : state) := match x with |  state'mk _ a _ _ _ _ _ => a end.
Definition values (x : state) := match x with |  state'mk _ _ a _ _ _ _ => a end.
Definition stack_sizes (x : state) := match x with |  state'mk _ _ _ a _ _ _ => a end.
Definition stacks1 (x : state) := match x with |  state'mk _ _ _ _ a _ _ => a end.
Definition positions (x : state) := match x with |  state'mk _ _ _ _ _ a _ => a end.
Definition preds (x : state) := match x with |  state'mk _ _ _ _ _ _ a => a end.
Definition inv (s : state) := (0%Z ≤ num_stacks s ∧ num_stacks s ≤ num_elts s) ∧ (0%Z < num_elts s -> 0%Z < num_stacks s) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < num_stacks s -> 1%Z ≤ stack_sizes s i ∧ (∀(j : Z), 0%Z ≤ j ∧ j < stack_sizes s i -> 0%Z ≤ stacks1 s i j ∧ stacks1 s i j < num_elts s)) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < num_elts s -> (match positions s i with | (is, ip) => (0%Z ≤ is ∧ is < num_stacks s) ∧ (0%Z ≤ ip ∧ ip < stack_sizes s is) ∧ stacks1 s is ip = i end)) ∧ (∀(is : Z), 0%Z ≤ is ∧ is < num_stacks s -> (∀(ip : Z), 0%Z ≤ ip ∧ ip < stack_sizes s is -> (is, ip) = positions s (stacks1 s is ip))) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < num_stacks s -> (let stack_i : Z -> Z := stacks1 s i in ∀(j : Z) (k : Z), 0%Z ≤ j ∧ j < k ∧ k < stack_sizes s i -> stack_i j < stack_i k)) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < num_stacks s -> (let stack_i : Z -> Z := stacks1 s i in ∀(j : Z) (k : Z), 0%Z ≤ j ∧ j ≤ k ∧ k < stack_sizes s i -> values s (stack_i k) ≤ values s (stack_i j))) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < num_elts s -> (let pred : Z := preds s i in (- 1%Z ≤ pred ∧ pred < num_elts s) ∧ pred < i ∧ (match positions s i with | (is, x_ip) => (if decide (pred < 0%Z) then is = 0%Z else values s pred < values s i ∧ 0%Z < is ∧ (match positions s pred with | (ps, x_pp) => ps = is - 1%Z end)) end))).
Inductive seq (α : Type) :=
  | seq'mk : Z -> (Z -> α) -> seq α.
Axiom seq_inhabited : forall  {α : Type} `{Inhabited α}, Inhabited (seq α).
Global Existing Instance seq_inhabited.
Arguments seq'mk {α}.
Definition seqlen {α : Type} (x : seq α) := match x with |  seq'mk a _ => a end.
Definition seqval {α : Type} (x : seq α) := match x with |  seq'mk _ a => a end.
Definition increasing_subsequence (s : seq Z) (l : list Z) := (0%Z ≤ seqlen s ∧ seqlen s ≤ Z.of_nat (length l)) ∧ ((∀(i : Z), 0%Z ≤ i ∧ i < seqlen s -> 0%Z ≤ seqval s i ∧ seqval s i < Z.of_nat (length l)) ∧ (∀(i : Z) (j : Z), 0%Z ≤ i ∧ i < j ∧ j < seqlen s -> seqval s i < seqval s j)) ∧ (∀(i : Z) (j : Z), 0%Z ≤ i ∧ i < j ∧ j < seqlen s -> nth (Z.to_nat (seqval s i)) l inhabitant < nth (Z.to_nat (seqval s j)) l inhabitant).
Theorem play_game'vc (input : list Z) : let o1 : Z -> Z := (const : Z -> Z -> Z) (- 1%Z) in inv (state'mk 0%Z 0%Z o1 ((const : Z -> Z -> Z) 0%Z) ((const : (Z -> Z) -> Z -> Z -> Z) ((const : Z -> Z -> Z) (- 1%Z))) ((const : Z * Z -> Z -> Z * Z) (- 1%Z, - 1%Z)) ((const : Z -> Z -> Z) (- 1%Z))) ∧ (∀(s : state), inv s ∧ num_elts s = 0%Z + Z.of_nat (length input) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < 0%Z -> values s i = o1 i) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < num_elts s -> values s i = nth (Z.to_nat (i - 0%Z)) input inhabitant) -> (let ns : Z := num_stacks s in if decide (ns = 0%Z) then (∃(s1 : seq Z), seqlen s1 = num_stacks s ∧ increasing_subsequence s1 input) ∧ (∀(s1 : seq Z), increasing_subsequence s1 input -> seqlen s1 ≤ num_stacks s) else let o2 : Z := stacks1 s (ns - 1%Z) (stack_sizes s (ns - 1%Z) - 1%Z) in let o3 : Z -> Z := (const : Z -> Z -> Z) (- 1%Z) in let o4 : Z := ns - 1%Z in (0%Z - 1%Z ≤ o4 -> ((- 1%Z ≤ o2 ∧ o2 < num_elts s) ∧ (0%Z ≤ o4 -> 0%Z ≤ o2 ∧ (match positions s o2 with | (is, _) => is = o4 end)) ∧ (o4 + 1%Z < ns -> o2 < o3 (o4 + 1%Z)) ∧ (0%Z ≤ o4 ∧ o4 < ns - 1%Z -> values s o2 < values s (o3 (o4 + 1%Z))) ∧ (∀(j : Z), o4 < j ∧ j < ns -> 0%Z ≤ o3 j ∧ o3 j < num_elts s) ∧ (∀(j : Z) (k : Z), o4 < j ∧ j < k ∧ k < ns -> o3 j < o3 k) ∧ (∀(j : Z) (k : Z), o4 < j ∧ j < k ∧ k < ns -> values s (o3 j) < values s (o3 k))) ∧ (∀(seq1 : Z -> Z) (idx : Z), (∀(i : Z), (i ≤ o4 ∧ 0%Z ≤ i) ∧ (- 1%Z ≤ idx ∧ idx < num_elts s) ∧ (0%Z ≤ i -> 0%Z ≤ idx ∧ (match positions s idx with | (is, _) => is = i end)) ∧ (i + 1%Z < ns -> idx < seq1 (i + 1%Z)) ∧ (0%Z ≤ i ∧ i < ns - 1%Z -> values s idx < values s (seq1 (i + 1%Z))) ∧ (∀(j : Z), i < j ∧ j < ns -> 0%Z ≤ seq1 j ∧ seq1 j < num_elts s) ∧ (∀(j : Z) (k : Z), i < j ∧ j < k ∧ k < ns -> seq1 j < seq1 k) ∧ (∀(j : Z) (k : Z), i < j ∧ j < k ∧ k < ns -> values s (seq1 j) < values s (seq1 k)) -> (- 1%Z ≤ preds s idx ∧ preds s idx < num_elts s) ∧ (0%Z ≤ i - 1%Z -> 0%Z ≤ preds s idx ∧ (match positions s (preds s idx) with | (is, _) => is = i - 1%Z end)) ∧ (i - 1%Z + 1%Z < ns -> preds s idx < fun_updt seq1 i idx (i - 1%Z + 1%Z)) ∧ (0%Z ≤ i - 1%Z ∧ i - 1%Z < ns - 1%Z -> values s (preds s idx) < values s (fun_updt seq1 i idx (i - 1%Z + 1%Z))) ∧ (∀(j : Z), i - 1%Z < j ∧ j < ns -> 0%Z ≤ fun_updt seq1 i idx j ∧ fun_updt seq1 i idx j < num_elts s) ∧ (∀(j : Z) (k : Z), i - 1%Z < j ∧ j < k ∧ k < ns -> fun_updt seq1 i idx j < fun_updt seq1 i idx k) ∧ (∀(j : Z) (k : Z), i - 1%Z < j ∧ j < k ∧ k < ns -> values s (fun_updt seq1 i idx j) < values s (fun_updt seq1 i idx k))) ∧ ((- 1%Z ≤ idx ∧ idx < num_elts s) ∧ (0%Z ≤ 0%Z - 1%Z -> 0%Z ≤ idx ∧ (match positions s idx with | (is, _) => is = 0%Z - 1%Z end)) ∧ (0%Z - 1%Z + 1%Z < ns -> idx < seq1 (0%Z - 1%Z + 1%Z)) ∧ (0%Z ≤ 0%Z - 1%Z ∧ 0%Z - 1%Z < ns - 1%Z -> values s idx < values s (seq1 (0%Z - 1%Z + 1%Z))) ∧ (∀(j : Z), 0%Z - 1%Z < j ∧ j < ns -> 0%Z ≤ seq1 j ∧ seq1 j < num_elts s) ∧ (∀(j : Z) (k : Z), 0%Z - 1%Z < j ∧ j < k ∧ k < ns -> seq1 j < seq1 k) ∧ (∀(j : Z) (k : Z), 0%Z - 1%Z < j ∧ j < k ∧ k < ns -> values s (seq1 j) < values s (seq1 k)) -> (∃(s1 : seq Z), seqlen s1 = num_stacks s ∧ increasing_subsequence s1 input) ∧ (∀(s1 : seq Z), increasing_subsequence s1 input -> seqlen s1 ≤ num_stacks s)))) ∧ (o4 < 0%Z - 1%Z -> (∃(s1 : seq Z), seqlen s1 = num_stacks s ∧ increasing_subsequence s1 input) ∧ (∀(s1 : seq Z), increasing_subsequence s1 input -> seqlen s1 ≤ num_stacks s)))).
Admitted.
