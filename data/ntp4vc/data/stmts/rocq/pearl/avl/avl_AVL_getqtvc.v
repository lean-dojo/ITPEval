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
Require Import avl.avl.SelectionTypes.
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
Axiom selector : Type.
Axiom selector_inhabited : Inhabited selector.
Global Existing Instance selector_inhabited.
Axiom selector_countable : Countable selector.
Global Existing Instance selector_countable.
Axiom selected : forall {α : Type} `{Inhabited α}, selector -> split (t1 α) -> Prop.
Axiom selection_possible : forall {α : Type} `{Inhabited α}, selector -> list (t1 α) -> Prop.
Axiom selection_empty : forall  {α : Type} `{Inhabited α} (s : selector), selection_possible s ([] : list (t1 α)) -> selected s (split'mk ([] : list (t1 α)) (None : option (t1 α)) ([] : list (t1 α))).
Axiom part : Type.
Axiom part_inhabited : Inhabited part.
Global Existing Instance part_inhabited.
Axiom part_countable : Countable part.
Global Existing Instance part_countable.
Theorem get'vc {α : Type} `{Inhabited α} (s : selector) (t3 : t2 α) (o1 : view α) (fact0 : selection_possible s (seq (m1 t3))) (fact1 : match o1 with | AEmpty => hgt (m1 t3) = 0%Z ∧ seq (m1 t3) = ([] : list (t1 α)) | ANode l d r h s1 => seq (m1 t3) = node_model (seq (m1 l)) d (seq (m1 r)) ∧ s1 = agg measure_closure (seq (m1 t3)) ∧ (let hl : Z := hgt (m1 l) in let hr : Z := hgt (m1 r) in (- Z.of_nat balancing ≤ hl - hr ∧ hl - hr ≤ Z.of_nat balancing) ∧ hgt (m1 t3) = Z.of_nat h ∧ Z.of_nat h = 1%Z + (if decide (hl < hr) then hr else hl)) end) : match o1 with | AEmpty => (selected s (split'mk ([] : list (t1 α)) (None : option (t1 α)) ([] : list (t1 α))) ∧ rebuild (split'mk ([] : list (t1 α)) (None : option (t1 α)) ([] : list (t1 α))) = seq (m1 t3)) ∧ middle (split'mk ([] : list (t1 α)) (None : option (t1 α)) ([] : list (t1 α))) = (None : option (t1 α)) | ANode tl td tr _ _ => (let o2 : list (t1 α) := seq (m1 tr) in let o3 : list (t1 α) := seq (m1 tl) in (selection_possible s (node_model o3 td o2) ∧ agg measure_closure (seq (m1 tl)) = agg measure_closure o3 ∧ agg measure_closure (seq (m1 tr)) = agg measure_closure o2) ∧ (∀(o4 : part_base selector), (match o4 with | Here => selected s (split'mk o3 (Some td) o2) | Left sl => selection_possible sl o3 ∧ (∀(e : split (t1 α)), selected sl e ∧ rebuild e = o3 -> selected s (right_extend e td o2)) | Right sr => selection_possible sr o2 ∧ (∀(e : split (t1 α)), selected sr e ∧ rebuild e = o2 -> selected s (left_extend o3 td e)) end) -> (match o4 with | Left sl => ((0%Z ≤ hgt (m1 t3) ∧ hgt (m1 tl) < hgt (m1 t3)) ∧ selection_possible sl (seq (m1 tl))) ∧ (∀(r : split (t1 α)) (res : option (t1 α)), (selected sl r ∧ rebuild r = seq (m1 tl)) ∧ (match res with | None => middle r = (None : option (t1 α)) | Some d => middle r = Some d end) -> (selected s (right_extend r td (seq (m1 tr))) ∧ rebuild (right_extend r td (seq (m1 tr))) = seq (m1 t3)) ∧ (match res with | None => middle (right_extend r td (seq (m1 tr))) = (None : option (t1 α)) | Some d => middle (right_extend r td (seq (m1 tr))) = Some d end)) | Right sr => ((0%Z ≤ hgt (m1 t3) ∧ hgt (m1 tr) < hgt (m1 t3)) ∧ selection_possible sr (seq (m1 tr))) ∧ (∀(r : split (t1 α)) (res : option (t1 α)), (selected sr r ∧ rebuild r = seq (m1 tr)) ∧ (match res with | None => middle r = (None : option (t1 α)) | Some d => middle r = Some d end) -> (selected s (left_extend (seq (m1 tl)) td r) ∧ rebuild (left_extend (seq (m1 tl)) td r) = seq (m1 t3)) ∧ (match res with | None => middle (left_extend (seq (m1 tl)) td r) = (None : option (t1 α)) | Some d => middle (left_extend (seq (m1 tl)) td r) = Some d end)) | Here => (selected s (split'mk (seq (m1 tl)) (Some td) (seq (m1 tr))) ∧ rebuild (split'mk (seq (m1 tl)) (Some td) (seq (m1 tr))) = seq (m1 t3)) ∧ middle (split'mk (seq (m1 tl)) (Some td) (seq (m1 tr))) = Some td end))) end.
Admitted.
