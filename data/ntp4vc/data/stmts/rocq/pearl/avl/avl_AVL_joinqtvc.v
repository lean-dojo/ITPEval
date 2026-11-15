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
Theorem join'vc {α : Type} `{Inhabited α} (o1 : view α) (l : t2 α) (r : t2 α) (d : t1 α) (fact0 : match o1 with | AEmpty => hgt (m1 l) = 0%Z ∧ seq (m1 l) = ([] : list (t1 α)) | ANode l1 d r h s => seq (m1 l) = node_model (seq (m1 l1)) d (seq (m1 r)) ∧ s = agg measure_closure (seq (m1 l)) ∧ (let hl : Z := hgt (m1 l1) in let hr : Z := hgt (m1 r) in (- Z.of_nat balancing ≤ hl - hr ∧ hl - hr ≤ Z.of_nat balancing) ∧ hgt (m1 l) = Z.of_nat h ∧ Z.of_nat h = 1%Z + (if decide (hl < hr) then hr else hl)) end) : (match o1 with | AEmpty => True | ANode ll ld lr lh _ => (∀(o2 : view α), (match o2 with | AEmpty => hgt (m1 r) = 0%Z ∧ seq (m1 r) = ([] : list (t1 α)) | ANode l1 d r1 h s => seq (m1 r) = node_model (seq (m1 l1)) d (seq (m1 r1)) ∧ s = agg measure_closure (seq (m1 r)) ∧ (let hl : Z := hgt (m1 l1) in let hr : Z := hgt (m1 r1) in (- Z.of_nat balancing ≤ hl - hr ∧ hl - hr ≤ Z.of_nat balancing) ∧ hgt (m1 r) = Z.of_nat h ∧ Z.of_nat h = 1%Z + (if decide (hl < hr) then hr else hl)) end) -> (match o2 with | AEmpty => True | ANode rl rd rr rh _ => (∀(o3 : nat), Z.of_nat o3 = - Z.of_nat rh -> (Z.of_nat o3 ≤ Z.of_nat lh - Z.of_nat rh ∧ Z.of_nat lh - Z.of_nat rh ≤ Z.of_nat lh) ∧ (∀(df : nat), Z.of_nat df = Z.of_nat lh - Z.of_nat rh -> (if decide (Z.of_nat balancing < Z.of_nat df) then (0%Z ≤ (if decide (hgt (m1 r) < hgt (m1 l)) then hgt (m1 l) - hgt (m1 r) else hgt (m1 r) - hgt (m1 l)) ∧ (if decide (hgt (m1 r) < hgt (m1 lr)) then hgt (m1 lr) - hgt (m1 r) else hgt (m1 r) - hgt (m1 lr)) < (if decide (hgt (m1 r) < hgt (m1 l)) then hgt (m1 l) - hgt (m1 r) else hgt (m1 r) - hgt (m1 l))) ∧ (∀(o4 : t2 α), seq (m1 o4) = node_model (seq (m1 lr)) d (seq (m1 r)) ∧ (let hl : Z := hgt (m1 lr) in let hr : Z := hgt (m1 r) in let he : Z := 1%Z + (if decide (hl < hr) then hr else hl) in let hres : Z := hgt (m1 o4) in 0%Z ≤ he - hres ∧ he - hres ≤ 1%Z) -> - Z.of_nat balancing - 1%Z ≤ hgt (m1 ll) - hgt (m1 o4) ∧ hgt (m1 ll) - hgt (m1 o4) ≤ Z.of_nat balancing + 1%Z) else ∀(o4 : nat), Z.of_nat o4 = - Z.of_nat balancing -> (if decide (Z.of_nat df < Z.of_nat o4) then (0%Z ≤ (if decide (hgt (m1 r) < hgt (m1 l)) then hgt (m1 l) - hgt (m1 r) else hgt (m1 r) - hgt (m1 l)) ∧ (if decide (hgt (m1 rl) < hgt (m1 l)) then hgt (m1 l) - hgt (m1 rl) else hgt (m1 rl) - hgt (m1 l)) < (if decide (hgt (m1 r) < hgt (m1 l)) then hgt (m1 l) - hgt (m1 r) else hgt (m1 r) - hgt (m1 l))) ∧ (∀(o5 : t2 α), seq (m1 o5) = node_model (seq (m1 l)) d (seq (m1 rl)) ∧ (let hl : Z := hgt (m1 l) in let hr : Z := hgt (m1 rl) in let he : Z := 1%Z + (if decide (hl < hr) then hr else hl) in let hres : Z := hgt (m1 o5) in 0%Z ≤ he - hres ∧ he - hres ≤ 1%Z) -> - Z.of_nat balancing - 1%Z ≤ hgt (m1 o5) - hgt (m1 rr) ∧ hgt (m1 o5) - hgt (m1 rr) ≤ Z.of_nat balancing + 1%Z) else - Z.of_nat balancing ≤ hgt (m1 l) - hgt (m1 r) ∧ hgt (m1 l) - hgt (m1 r) ≤ Z.of_nat balancing)))) end)) end) ∧ (∀(result : t2 α), (match o1 with | AEmpty => seq (m1 result) = cons d (seq (m1 r)) ∧ hgt (m1 result) - hgt (m1 r) ≤ 1%Z ∧ 0%Z ≤ hgt (m1 result) - hgt (m1 r) | ANode ll ld lr lh _ => (∃(o2 : view α), (match o2 with | AEmpty => hgt (m1 r) = 0%Z ∧ seq (m1 r) = ([] : list (t1 α)) | ANode l1 d1 r1 h s => seq (m1 r) = node_model (seq (m1 l1)) d1 (seq (m1 r1)) ∧ s = agg measure_closure (seq (m1 r)) ∧ (let hl : Z := hgt (m1 l1) in let hr : Z := hgt (m1 r1) in (- Z.of_nat balancing ≤ hl - hr ∧ hl - hr ≤ Z.of_nat balancing) ∧ hgt (m1 r) = Z.of_nat h ∧ Z.of_nat h = 1%Z + (if decide (hl < hr) then hr else hl)) end) ∧ (match o2 with | AEmpty => seq (m1 result) = seq (m1 l) ++ [d] ∧ hgt (m1 result) - hgt (m1 l) ≤ 1%Z ∧ 0%Z ≤ hgt (m1 result) - hgt (m1 l) | ANode rl rd rr rh _ => (∃(o3 : nat), Z.of_nat o3 = - Z.of_nat rh ∧ (∃(df : nat), Z.of_nat df = Z.of_nat lh - Z.of_nat rh ∧ (if decide (Z.of_nat balancing < Z.of_nat df) then ∃(o4 : t2 α), (seq (m1 o4) = node_model (seq (m1 lr)) d (seq (m1 r)) ∧ (let hl : Z := hgt (m1 lr) in let hr : Z := hgt (m1 r) in let he : Z := 1%Z + (if decide (hl < hr) then hr else hl) in let hres : Z := hgt (m1 o4) in 0%Z ≤ he - hres ∧ he - hres ≤ 1%Z)) ∧ seq (m1 result) = node_model (seq (m1 ll)) ld (seq (m1 o4)) ∧ (let hl : Z := hgt (m1 ll) in let hr : Z := hgt (m1 o4) in let he : Z := 1%Z + (if decide (hl < hr) then hr else hl) in let hres : Z := hgt (m1 result) in (0%Z ≤ he - hres ∧ he - hres ≤ 1%Z) ∧ (- Z.of_nat balancing ≤ hl - hr ∧ hl - hr ≤ Z.of_nat balancing -> he = hres)) else ∃(o4 : nat), Z.of_nat o4 = - Z.of_nat balancing ∧ (if decide (Z.of_nat df < Z.of_nat o4) then ∃(o5 : t2 α), (seq (m1 o5) = node_model (seq (m1 l)) d (seq (m1 rl)) ∧ (let hl : Z := hgt (m1 l) in let hr : Z := hgt (m1 rl) in let he : Z := 1%Z + (if decide (hl < hr) then hr else hl) in let hres : Z := hgt (m1 o5) in 0%Z ≤ he - hres ∧ he - hres ≤ 1%Z)) ∧ seq (m1 result) = node_model (seq (m1 o5)) rd (seq (m1 rr)) ∧ (let hl : Z := hgt (m1 o5) in let hr : Z := hgt (m1 rr) in let he : Z := 1%Z + (if decide (hl < hr) then hr else hl) in let hres : Z := hgt (m1 result) in (0%Z ≤ he - hres ∧ he - hres ≤ 1%Z) ∧ (- Z.of_nat balancing ≤ hl - hr ∧ hl - hr ≤ Z.of_nat balancing -> he = hres)) else seq (m1 result) = node_model (seq (m1 l)) d (seq (m1 r)) ∧ hgt (m1 result) = 1%Z + (if decide (hgt (m1 l) < hgt (m1 r)) then hgt (m1 r) else hgt (m1 l)))))) end)) end) -> seq (m1 result) = node_model (seq (m1 l)) d (seq (m1 r)) ∧ (let hl : Z := hgt (m1 l) in let hr : Z := hgt (m1 r) in let he : Z := 1%Z + (if decide (hl < hr) then hr else hl) in let hres : Z := hgt (m1 result) in 0%Z ≤ he - hres ∧ he - hres ≤ 1%Z)).
Admitted.
