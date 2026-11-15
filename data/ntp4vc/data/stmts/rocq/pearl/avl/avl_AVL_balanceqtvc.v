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
Theorem balance'vc {α : Type} `{Inhabited α} (l : t2 α) (r : t2 α) (hl : nat) (hr : nat) (o1 : nat) (d : t1 α) (fact0 : - Z.of_nat balancing - 1%Z ≤ hgt (m1 l) - hgt (m1 r)) (fact1 : hgt (m1 l) - hgt (m1 r) ≤ Z.of_nat balancing + 1%Z) (fact2 : Z.of_nat hl = hgt (m1 l)) (fact3 : Z.of_nat hr = hgt (m1 r)) (fact4 : Z.of_nat o1 = - Z.of_nat hr) : Z.of_nat o1 ≤ Z.of_nat hl - Z.of_nat hr ∧ Z.of_nat hl - Z.of_nat hr ≤ Z.of_nat hl ∧ (∀(df : nat), Z.of_nat df = Z.of_nat hl - Z.of_nat hr -> (if decide (Z.of_nat balancing < Z.of_nat df) then ∀(o2 : view α), (match o2 with | AEmpty => hgt (m1 l) = 0%Z ∧ seq (m1 l) = ([] : list (t1 α)) | ANode l1 d r1 h s => seq (m1 l) = node_model (seq (m1 l1)) d (seq (m1 r1)) ∧ s = agg measure_closure (seq (m1 l)) ∧ (let hl1 : Z := hgt (m1 l1) in let hr1 : Z := hgt (m1 r1) in (- Z.of_nat balancing ≤ hl1 - hr1 ∧ hl1 - hr1 ≤ Z.of_nat balancing) ∧ hgt (m1 l) = Z.of_nat h ∧ Z.of_nat h = 1%Z + (if decide (hl1 < hr1) then hr1 else hl1)) end) -> (match o2 with | AEmpty => False | ANode ll ld lr _ _ => (∀(o3 : nat), Z.of_nat o3 = hgt (m1 lr) -> (∀(o4 : nat), Z.of_nat o4 = hgt (m1 ll) -> (if decide (Z.of_nat o3 ≤ Z.of_nat o4) then (- Z.of_nat balancing ≤ hgt (m1 lr) - hgt (m1 r) ∧ hgt (m1 lr) - hgt (m1 r) ≤ Z.of_nat balancing) ∧ (∀(o5 : t2 α), seq (m1 o5) = node_model (seq (m1 lr)) d (seq (m1 r)) ∧ hgt (m1 o5) = 1%Z + (if decide (hgt (m1 lr) < hgt (m1 r)) then hgt (m1 r) else hgt (m1 lr)) -> - Z.of_nat balancing ≤ hgt (m1 ll) - hgt (m1 o5) ∧ hgt (m1 ll) - hgt (m1 o5) ≤ Z.of_nat balancing) else ∀(o5 : view α), (match o5 with | AEmpty => hgt (m1 lr) = 0%Z ∧ seq (m1 lr) = ([] : list (t1 α)) | ANode l1 d1 r1 h s => seq (m1 lr) = node_model (seq (m1 l1)) d1 (seq (m1 r1)) ∧ s = agg measure_closure (seq (m1 lr)) ∧ (let hl1 : Z := hgt (m1 l1) in let hr1 : Z := hgt (m1 r1) in (- Z.of_nat balancing ≤ hl1 - hr1 ∧ hl1 - hr1 ≤ Z.of_nat balancing) ∧ hgt (m1 lr) = Z.of_nat h ∧ Z.of_nat h = 1%Z + (if decide (hl1 < hr1) then hr1 else hl1)) end) -> (match o5 with | AEmpty => False | ANode lrl lrd lrr _ _ => (- Z.of_nat balancing ≤ hgt (m1 lrr) - hgt (m1 r) ∧ hgt (m1 lrr) - hgt (m1 r) ≤ Z.of_nat balancing) ∧ (∀(o6 : t2 α), seq (m1 o6) = node_model (seq (m1 lrr)) d (seq (m1 r)) ∧ hgt (m1 o6) = 1%Z + (if decide (hgt (m1 lrr) < hgt (m1 r)) then hgt (m1 r) else hgt (m1 lrr)) -> (- Z.of_nat balancing ≤ hgt (m1 ll) - hgt (m1 lrl) ∧ hgt (m1 ll) - hgt (m1 lrl) ≤ Z.of_nat balancing) ∧ (∀(o7 : t2 α), seq (m1 o7) = node_model (seq (m1 ll)) ld (seq (m1 lrl)) ∧ hgt (m1 o7) = 1%Z + (if decide (hgt (m1 ll) < hgt (m1 lrl)) then hgt (m1 lrl) else hgt (m1 ll)) -> - Z.of_nat balancing ≤ hgt (m1 o7) - hgt (m1 o6) ∧ hgt (m1 o7) - hgt (m1 o6) ≤ Z.of_nat balancing)) end)))) end) else ∀(o2 : nat), Z.of_nat o2 = - Z.of_nat balancing -> (if decide (Z.of_nat df < Z.of_nat o2) then ∀(o3 : view α), (match o3 with | AEmpty => hgt (m1 r) = 0%Z ∧ seq (m1 r) = ([] : list (t1 α)) | ANode l1 d1 r1 h s => seq (m1 r) = node_model (seq (m1 l1)) d1 (seq (m1 r1)) ∧ s = agg measure_closure (seq (m1 r)) ∧ (let hl1 : Z := hgt (m1 l1) in let hr1 : Z := hgt (m1 r1) in (- Z.of_nat balancing ≤ hl1 - hr1 ∧ hl1 - hr1 ≤ Z.of_nat balancing) ∧ hgt (m1 r) = Z.of_nat h ∧ Z.of_nat h = 1%Z + (if decide (hl1 < hr1) then hr1 else hl1)) end) -> (match o3 with | AEmpty => False | ANode rl rd rr _ _ => (∀(o4 : nat), Z.of_nat o4 = hgt (m1 rl) -> (∀(o5 : nat), Z.of_nat o5 = hgt (m1 rr) -> (if decide (Z.of_nat o4 ≤ Z.of_nat o5) then (- Z.of_nat balancing ≤ hgt (m1 l) - hgt (m1 rl) ∧ hgt (m1 l) - hgt (m1 rl) ≤ Z.of_nat balancing) ∧ (∀(o6 : t2 α), seq (m1 o6) = node_model (seq (m1 l)) d (seq (m1 rl)) ∧ hgt (m1 o6) = 1%Z + (if decide (hgt (m1 l) < hgt (m1 rl)) then hgt (m1 rl) else hgt (m1 l)) -> - Z.of_nat balancing ≤ hgt (m1 o6) - hgt (m1 rr) ∧ hgt (m1 o6) - hgt (m1 rr) ≤ Z.of_nat balancing) else ∀(o6 : view α), (match o6 with | AEmpty => hgt (m1 rl) = 0%Z ∧ seq (m1 rl) = ([] : list (t1 α)) | ANode l1 d1 r1 h s => seq (m1 rl) = node_model (seq (m1 l1)) d1 (seq (m1 r1)) ∧ s = agg measure_closure (seq (m1 rl)) ∧ (let hl1 : Z := hgt (m1 l1) in let hr1 : Z := hgt (m1 r1) in (- Z.of_nat balancing ≤ hl1 - hr1 ∧ hl1 - hr1 ≤ Z.of_nat balancing) ∧ hgt (m1 rl) = Z.of_nat h ∧ Z.of_nat h = 1%Z + (if decide (hl1 < hr1) then hr1 else hl1)) end) -> (match o6 with | AEmpty => False | ANode rll rld rlr _ _ => (- Z.of_nat balancing ≤ hgt (m1 rlr) - hgt (m1 rr) ∧ hgt (m1 rlr) - hgt (m1 rr) ≤ Z.of_nat balancing) ∧ (∀(o7 : t2 α), seq (m1 o7) = node_model (seq (m1 rlr)) rd (seq (m1 rr)) ∧ hgt (m1 o7) = 1%Z + (if decide (hgt (m1 rlr) < hgt (m1 rr)) then hgt (m1 rr) else hgt (m1 rlr)) -> (- Z.of_nat balancing ≤ hgt (m1 l) - hgt (m1 rll) ∧ hgt (m1 l) - hgt (m1 rll) ≤ Z.of_nat balancing) ∧ (∀(o8 : t2 α), seq (m1 o8) = node_model (seq (m1 l)) d (seq (m1 rll)) ∧ hgt (m1 o8) = 1%Z + (if decide (hgt (m1 l) < hgt (m1 rll)) then hgt (m1 rll) else hgt (m1 l)) -> - Z.of_nat balancing ≤ hgt (m1 o8) - hgt (m1 o7) ∧ hgt (m1 o8) - hgt (m1 o7) ≤ Z.of_nat balancing)) end)))) end) else - Z.of_nat balancing ≤ hgt (m1 l) - hgt (m1 r) ∧ hgt (m1 l) - hgt (m1 r) ≤ Z.of_nat balancing)) ∧ (∀(result : t2 α), (if decide (Z.of_nat balancing < Z.of_nat df) then ∃(o2 : view α), (match o2 with | AEmpty => hgt (m1 l) = 0%Z ∧ seq (m1 l) = ([] : list (t1 α)) | ANode l1 d1 r1 h s => seq (m1 l) = node_model (seq (m1 l1)) d1 (seq (m1 r1)) ∧ s = agg measure_closure (seq (m1 l)) ∧ (let hl1 : Z := hgt (m1 l1) in let hr1 : Z := hgt (m1 r1) in (- Z.of_nat balancing ≤ hl1 - hr1 ∧ hl1 - hr1 ≤ Z.of_nat balancing) ∧ hgt (m1 l) = Z.of_nat h ∧ Z.of_nat h = 1%Z + (if decide (hl1 < hr1) then hr1 else hl1)) end) ∧ (match o2 with | AEmpty => False | ANode ll ld lr _ _ => (∃(o3 : nat), Z.of_nat o3 = hgt (m1 lr) ∧ (∃(o4 : nat), Z.of_nat o4 = hgt (m1 ll) ∧ (if decide (Z.of_nat o3 ≤ Z.of_nat o4) then ∃(o5 : t2 α), (seq (m1 o5) = node_model (seq (m1 lr)) d (seq (m1 r)) ∧ hgt (m1 o5) = 1%Z + (if decide (hgt (m1 lr) < hgt (m1 r)) then hgt (m1 r) else hgt (m1 lr))) ∧ seq (m1 result) = node_model (seq (m1 ll)) ld (seq (m1 o5)) ∧ hgt (m1 result) = 1%Z + (if decide (hgt (m1 ll) < hgt (m1 o5)) then hgt (m1 o5) else hgt (m1 ll)) else ∃(o5 : view α), (match o5 with | AEmpty => hgt (m1 lr) = 0%Z ∧ seq (m1 lr) = ([] : list (t1 α)) | ANode l1 d1 r1 h s => seq (m1 lr) = node_model (seq (m1 l1)) d1 (seq (m1 r1)) ∧ s = agg measure_closure (seq (m1 lr)) ∧ (let hl1 : Z := hgt (m1 l1) in let hr1 : Z := hgt (m1 r1) in (- Z.of_nat balancing ≤ hl1 - hr1 ∧ hl1 - hr1 ≤ Z.of_nat balancing) ∧ hgt (m1 lr) = Z.of_nat h ∧ Z.of_nat h = 1%Z + (if decide (hl1 < hr1) then hr1 else hl1)) end) ∧ (match o5 with | AEmpty => False | ANode lrl lrd lrr _ _ => (∃(o6 : t2 α), (seq (m1 o6) = node_model (seq (m1 lrr)) d (seq (m1 r)) ∧ hgt (m1 o6) = 1%Z + (if decide (hgt (m1 lrr) < hgt (m1 r)) then hgt (m1 r) else hgt (m1 lrr))) ∧ (∃(o7 : t2 α), (seq (m1 o7) = node_model (seq (m1 ll)) ld (seq (m1 lrl)) ∧ hgt (m1 o7) = 1%Z + (if decide (hgt (m1 ll) < hgt (m1 lrl)) then hgt (m1 lrl) else hgt (m1 ll))) ∧ seq (m1 result) = node_model (seq (m1 o7)) lrd (seq (m1 o6)) ∧ hgt (m1 result) = 1%Z + (if decide (hgt (m1 o7) < hgt (m1 o6)) then hgt (m1 o6) else hgt (m1 o7)))) end)))) end) else ∃(o2 : nat), Z.of_nat o2 = - Z.of_nat balancing ∧ (if decide (Z.of_nat df < Z.of_nat o2) then ∃(o3 : view α), (match o3 with | AEmpty => hgt (m1 r) = 0%Z ∧ seq (m1 r) = ([] : list (t1 α)) | ANode l1 d1 r1 h s => seq (m1 r) = node_model (seq (m1 l1)) d1 (seq (m1 r1)) ∧ s = agg measure_closure (seq (m1 r)) ∧ (let hl1 : Z := hgt (m1 l1) in let hr1 : Z := hgt (m1 r1) in (- Z.of_nat balancing ≤ hl1 - hr1 ∧ hl1 - hr1 ≤ Z.of_nat balancing) ∧ hgt (m1 r) = Z.of_nat h ∧ Z.of_nat h = 1%Z + (if decide (hl1 < hr1) then hr1 else hl1)) end) ∧ (match o3 with | AEmpty => False | ANode rl rd rr _ _ => (∃(o4 : nat), Z.of_nat o4 = hgt (m1 rl) ∧ (∃(o5 : nat), Z.of_nat o5 = hgt (m1 rr) ∧ (if decide (Z.of_nat o4 ≤ Z.of_nat o5) then ∃(o6 : t2 α), (seq (m1 o6) = node_model (seq (m1 l)) d (seq (m1 rl)) ∧ hgt (m1 o6) = 1%Z + (if decide (hgt (m1 l) < hgt (m1 rl)) then hgt (m1 rl) else hgt (m1 l))) ∧ seq (m1 result) = node_model (seq (m1 o6)) rd (seq (m1 rr)) ∧ hgt (m1 result) = 1%Z + (if decide (hgt (m1 o6) < hgt (m1 rr)) then hgt (m1 rr) else hgt (m1 o6)) else ∃(o6 : view α), (match o6 with | AEmpty => hgt (m1 rl) = 0%Z ∧ seq (m1 rl) = ([] : list (t1 α)) | ANode l1 d1 r1 h s => seq (m1 rl) = node_model (seq (m1 l1)) d1 (seq (m1 r1)) ∧ s = agg measure_closure (seq (m1 rl)) ∧ (let hl1 : Z := hgt (m1 l1) in let hr1 : Z := hgt (m1 r1) in (- Z.of_nat balancing ≤ hl1 - hr1 ∧ hl1 - hr1 ≤ Z.of_nat balancing) ∧ hgt (m1 rl) = Z.of_nat h ∧ Z.of_nat h = 1%Z + (if decide (hl1 < hr1) then hr1 else hl1)) end) ∧ (match o6 with | AEmpty => False | ANode rll rld rlr _ _ => (∃(o7 : t2 α), (seq (m1 o7) = node_model (seq (m1 rlr)) rd (seq (m1 rr)) ∧ hgt (m1 o7) = 1%Z + (if decide (hgt (m1 rlr) < hgt (m1 rr)) then hgt (m1 rr) else hgt (m1 rlr))) ∧ (∃(o8 : t2 α), (seq (m1 o8) = node_model (seq (m1 l)) d (seq (m1 rll)) ∧ hgt (m1 o8) = 1%Z + (if decide (hgt (m1 l) < hgt (m1 rll)) then hgt (m1 rll) else hgt (m1 l))) ∧ seq (m1 result) = node_model (seq (m1 o8)) rld (seq (m1 o7)) ∧ hgt (m1 result) = 1%Z + (if decide (hgt (m1 o8) < hgt (m1 o7)) then hgt (m1 o7) else hgt (m1 o8)))) end)))) end) else seq (m1 result) = node_model (seq (m1 l)) d (seq (m1 r)) ∧ hgt (m1 result) = 1%Z + (if decide (hgt (m1 l) < hgt (m1 r)) then hgt (m1 r) else hgt (m1 l)))) -> seq (m1 result) = node_model (seq (m1 l)) d (seq (m1 r)) ∧ (let hl1 : Z := hgt (m1 l) in let hr1 : Z := hgt (m1 r) in let he : Z := 1%Z + (if decide (hl1 < hr1) then hr1 else hl1) in let hres : Z := hgt (m1 result) in (0%Z ≤ he - hres ∧ he - hres ≤ 1%Z) ∧ (- Z.of_nat balancing ≤ hl1 - hr1 ∧ hl1 - hr1 ≤ Z.of_nat balancing -> he = hres)))).
Admitted.
