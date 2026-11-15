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
Theorem play_cards'vc (s : state) (input : list Z) (fact0 : inv s) : match input with | [] => inv s ∧ num_elts s = num_elts s + Z.of_nat (length input) ∧ (∀(i : Z), num_elts s ≤ i ∧ i < num_elts s -> values s i = nth (Z.to_nat (i - num_elts s)) input inhabitant) | cons c rem => inv s ∧ (∀(s1 : state), inv s1 ∧ num_elts s1 = num_elts s + 1%Z ∧ values s1 = fun_updt (values s) (num_elts s) c -> ((match input with | [] => False | cons _ f => f = rem end) ∧ inv s1) ∧ (∀(s2 : state), inv s2 ∧ num_elts s2 = num_elts s1 + Z.of_nat (length rem) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < num_elts s1 -> values s2 i = values s1 i) ∧ (∀(i : Z), num_elts s1 ≤ i ∧ i < num_elts s2 -> values s2 i = nth (Z.to_nat (i - num_elts s1)) rem inhabitant) -> inv s2 ∧ num_elts s2 = num_elts s + Z.of_nat (length input) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < num_elts s -> values s2 i = values s i) ∧ (∀(i : Z), num_elts s ≤ i ∧ i < num_elts s2 -> values s2 i = nth (Z.to_nat (i - num_elts s)) input inhabitant))) end.
Admitted.
