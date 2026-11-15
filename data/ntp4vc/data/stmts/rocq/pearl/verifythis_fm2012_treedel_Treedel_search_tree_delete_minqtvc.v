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
Require Import verifythis_fm2012_treedel_vcg.verifythis_fm2012_treedel.Memory.
Require Import Why3.bintree.Tree.
Require Import Why3.bintree.Inorder.
Open Scope Z_scope.
Definition root (t : tree loc) : loc := match t with | Empty => null | Node _ p _ => p end.
Program Fixpoint istree (m : loc -> node) (t : tree loc) : Prop :=
match t with | Empty => True | Node l p r => ¬ p = null ∧ istree m l ∧ istree m r ∧ root l = left1 (m p) ∧ root r = right1 (m p) end.
Admit Obligations.
Inductive zipper (α : Type) :=
  | Top : zipper α
  | Left : zipper α -> α -> tree α -> zipper α.
Axiom zipper_inhabited : forall  {α : Type} `{Inhabited α}, Inhabited (zipper α).
Global Existing Instance zipper_inhabited.
Arguments Top {α}.
Arguments Left {α}.
Program Fixpoint zip {α : Type} `{Inhabited α} (t : tree α) (z : zipper α) : tree α :=
match z with | Top => t | Left z1 x r => zip (Node t x r) z1 end.
Admit Obligations.
Program Fixpoint inorderz {α : Type} `{Inhabited α} (z : zipper α) : list α :=
match z with | Top => ([] : list α) | Left z1 x r => cons x (inorder r) ++ inorderz z1 end.
Admit Obligations.
Theorem search_tree_delete_min'vc (it : tree loc) (mem : loc -> node) (fact0 : ¬ root it = null) (fact1 : istree mem it) (fact2 : NoDup (inorder it)) : ¬ root it = null ∧ (let o1 : loc := left1 (mem (root it)) in let o2 : loc := null in eq_loc o1 o2 = (o1 = o2) -> (if decide (eq_loc o1 o2) then ¬ root it = null ∧ ¬ root it = null ∧ (match it with | Empty => False | Node l _ r => istree mem r ∧ root r = right1 (mem (root it)) ∧ (match inorder it with | [] => False | cons p l1 => data (mem (root it)) = data (mem p) ∧ inorder r = l1 end) end) else ¬ o1 = null ∧ ¬ it = (Empty : tree loc) ∧ (∀(o3 : tree loc), (match it with | Empty => False | Node _ _ r => o3 = r end) -> ¬ it = (Empty : tree loc) ∧ (∀(o4 : tree loc), (match it with | Empty => False | Node l _ _ => o4 = l end) -> ((¬ root it = null ∧ left1 (mem (root it)) = o1) ∧ ¬ o1 = null ∧ (let pt : tree loc := Node o4 (root it) o3 in istree mem pt ∧ zip pt Top = it)) ∧ (∀(subtree : tree loc) (ppr : tree loc) (zipper1 : zipper loc) (pp : loc), ¬ pp = null ∧ ¬ left1 (mem pp) = null ∧ (let pt : tree loc := Node subtree pp ppr in istree mem pt ∧ zip pt zipper1 = it) -> (let o5 : loc := null in eq_loc (left1 (mem (left1 (mem pp)))) o5 = (left1 (mem (left1 (mem pp))) = o5) -> (if decide (¬ eq_loc (left1 (mem (left1 (mem pp)))) o5) then ¬ subtree = (Empty : tree loc) ∧ (∀(o6 : tree loc), (match subtree with | Empty => False | Node _ _ r => o6 = r end) -> ¬ subtree = (Empty : tree loc) ∧ (∀(o7 : tree loc), (match subtree with | Empty => False | Node l _ _ => o7 = l end) -> ¬ left1 (mem (left1 (mem pp))) = null ∧ (match subtree with | Empty => False | Node f _ f1 => f = o7 ∨ f1 = o7 end) ∧ ¬ left1 (mem pp) = null ∧ ¬ left1 (mem (left1 (mem pp))) = null ∧ (let pt : tree loc := Node o7 (left1 (mem pp)) o6 in istree mem pt ∧ zip pt (Left zipper1 pp ppr) = it))) else ¬ left1 (mem pp) = null ∧ ¬ left1 (mem pp) = null ∧ ¬ pp = null ∧ (∀(mem1 : loc -> node), mem1 pp = (let x_q' : node := mem pp in node'mk (right1 (mem (left1 (mem pp)))) (right1 x_q') (data x_q')) ∧ (∀(q : loc), ¬ q = pp -> mem1 q = mem q) -> ¬ subtree = (Empty : tree loc) ∧ (∀(pl : tree loc), (match subtree with | Empty => False | Node l _ _ => pl = l end) -> ¬ subtree = (Empty : tree loc) ∧ (∀(o6 : tree loc), (match subtree with | Empty => False | Node _ _ r => o6 = r end) -> (∀(p : loc), data (mem1 p) = data (mem p)) ∧ istree mem1 (zip o6 (Left zipper1 pp ppr)) ∧ root (zip o6 (Left zipper1 pp ppr)) = root it ∧ (match inorder it with | [] => False | cons p l => data (mem (left1 (mem pp))) = data (mem1 p) ∧ inorder (zip o6 (Left zipper1 pp ppr)) = l end))))))))))).
Admitted.
