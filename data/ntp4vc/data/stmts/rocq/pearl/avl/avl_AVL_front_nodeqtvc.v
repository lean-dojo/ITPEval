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
Open Scope Z_scope.
Axiom t : Type.
Axiom t_inhabited : Inhabited t.
Global Existing Instance t_inhabited.
Axiom t_countable : Countable t.
Global Existing Instance t_countable.
Axiom zero : t.
Axiom op : t -> t -> t.
Axiom assoc : forall  (a : t) (b : t) (c : t), op a (op b c) = op (op a b) c.
Axiom neutral : forall  (x : t), op x zero = x ∧ x = op zero x.
Axiom agg : forall {α : Type} `{Inhabited α}, (α -> t) -> list α -> t.
Axiom agg_empty : forall  {α : Type} `{Inhabited α} (f : α -> t), agg f ([] : list α) = zero.
Axiom agg_sing : forall  {α : Type} `{Inhabited α} (s : list α) (f : α -> t) (fact0 : Z.of_nat (length s) = 1%Z), agg f s = f (nth 0%nat s inhabitant).
Axiom agg_cat : forall  {α : Type} `{Inhabited α} (f : α -> t) (s1 : list α) (s2 : list α), agg f (s1 ++ s2) = op (agg f s1) (agg f s2).
Axiom t1 : Type -> Type.
Axiom t1_inhabited : forall  {α : Type} `{Inhabited α}, Inhabited (t1 α).
Global Existing Instance t1_inhabited.
Axiom measure : forall {α : Type} `{Inhabited α}, t1 α -> t.
Axiom balancing : nat.
Axiom balancing'def : 0%Z < Z.of_nat balancing.
Inductive tree (α : Type) :=
  | Empty : tree α
  | Node : tree α -> t1 α -> tree α -> nat -> t -> tree α.
Axiom tree_inhabited : forall  {α : Type} `{Inhabited α}, Inhabited (tree α).
Global Existing Instance tree_inhabited.
Arguments Empty {α}.
Arguments Node {α}.
Inductive m (α : Type) :=
  | m'mk : list (t1 α) -> Z -> m α.
Axiom m_inhabited : forall  {α : Type} `{Inhabited α}, Inhabited (m α).
Global Existing Instance m_inhabited.
Arguments m'mk {α}.
Definition seq {α : Type} (x : m α) := match x with |  m'mk a _ => a end.
Definition hgt {α : Type} (x : m α) := match x with |  m'mk _ a => a end.
Definition node_model {α : Type} `{Inhabited α} (l : list α) (d : α) (r : list α) : list α := l ++ cons d r.
Program Fixpoint seq_model {α : Type} `{Inhabited α} (t2 : tree α) : list (t1 α) :=
match t2 with | Empty => ([] : list (t1 α)) | Node l d r _ _ => node_model (seq_model l) d (seq_model r) end.
Admit Obligations.
Program Fixpoint real_height {α : Type} `{Inhabited α} (t2 : tree α) : Z :=
match t2 with | Empty => 0%Z | Node l _ r _ _ => (let hl : Z := real_height l in let hr : Z := real_height r in 1%Z + (if decide (hl < hr) then hr else hl)) end.
Admit Obligations.
Axiom measure_closure : forall {α : Type} `{Inhabited α}, t1 α -> t.
Axiom measure_closure_def : forall  {α : Type} `{Inhabited α} (y : t1 α), measure_closure y = measure y.
Program Fixpoint balanced {α : Type} `{Inhabited α} (t2 : tree α) : Prop :=
match t2 with | Empty => True | Node l _ r h m1 => Z.of_nat h = real_height t2 ∧ m1 = agg measure_closure (seq_model t2) ∧ (- Z.of_nat balancing ≤ real_height r - real_height l ∧ real_height r - real_height l ≤ Z.of_nat balancing) ∧ balanced l ∧ balanced r end.
Admit Obligations.
Axiom t2 : Type -> Type.
Axiom t2_inhabited : forall  {α : Type} `{Inhabited α}, Inhabited (t2 α).
Global Existing Instance t2_inhabited.
Axiom repr : forall {α : Type} `{Inhabited α}, t2 α -> tree α.
Axiom m1 : forall {α : Type} `{Inhabited α}, t2 α -> m α.
Axiom t'invariant : forall  {α : Type} `{Inhabited α} (self : t2 α), balanced (repr self) ∧ seq (m1 self) = seq_model (repr self) ∧ hgt (m1 self) = real_height (repr self).
Definition t'eq {α : Type} `{Inhabited α} (a : t2 α) (b : t2 α) := repr a = repr b ∧ m1 a = m1 b.
Axiom t'inj : forall  {α : Type} `{Inhabited α} (a : t2 α) (b : t2 α) (fact0 : t'eq a b), a = b.
Inductive view (α : Type) :=
  | AEmpty : view α
  | ANode : t2 α -> t1 α -> t2 α -> nat -> t -> view α.
Axiom view_inhabited : forall  {α : Type} `{Inhabited α}, Inhabited (view α).
Global Existing Instance view_inhabited.
Arguments AEmpty {α}.
Arguments ANode {α}.
Theorem front_node'vc {α : Type} `{Inhabited α} (o1 : view α) (l : t2 α) (d : t1 α) (fact0 : match o1 with | AEmpty => hgt (m1 l) = 0%Z ∧ seq (m1 l) = ([] : list (t1 α)) | ANode l1 d r h s => seq (m1 l) = node_model (seq (m1 l1)) d (seq (m1 r)) ∧ s = agg measure_closure (seq (m1 l)) ∧ (let hl : Z := hgt (m1 l1) in let hr : Z := hgt (m1 r) in (- Z.of_nat balancing ≤ hl - hr ∧ hl - hr ≤ Z.of_nat balancing) ∧ hgt (m1 l) = Z.of_nat h ∧ Z.of_nat h = 1%Z + (if decide (hl < hr) then hr else hl)) end) : (match o1 with | AEmpty => True | ANode l1 d2 _ _ _ => 0%Z ≤ hgt (m1 l) ∧ hgt (m1 l1) < hgt (m1 l) end) ∧ (∀(result : t1 α), (match o1 with | AEmpty => result = d | ANode l1 d2 _ _ _ => result = nth 0%nat (seq (m1 l1) ++ [d2]) inhabitant end) -> result = nth 0%nat (seq (m1 l) ++ [d]) inhabitant).
Admitted.
