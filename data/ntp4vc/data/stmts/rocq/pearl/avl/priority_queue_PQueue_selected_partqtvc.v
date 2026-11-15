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
Axiom balancing : nat.
Axiom balancing'def : 0%Z < Z.of_nat balancing.
Axiom t : Type -> Type.
Axiom t_inhabited : forall  {α : Type} `{Inhabited α}, Inhabited (t α).
Global Existing Instance t_inhabited.
Axiom t1 : Type.
Axiom t1_inhabited : Inhabited t1.
Global Existing Instance t1_inhabited.
Axiom t1_countable : Countable t1.
Global Existing Instance t1_countable.
Axiom key : forall {α : Type} `{Inhabited α}, t α -> t1.
Axiom le : t1 -> t1 -> Prop.
Axiom Refl : forall  (x : t1), le x x.
Axiom Trans : forall  (x : t1) (y : t1) (z : t1) (fact0 : le x y) (fact1 : le y z), le x z.
Axiom eq : t1 -> t1 -> Prop.
Axiom eq_def : forall  (x : t1) (y : t1), eq x y = (le x y ∧ le y x).
Axiom lt : t1 -> t1 -> Prop.
Axiom lt_def : forall  (x : t1) (y : t1), lt x y = (le x y ∧ ¬ le y x).
Axiom Total : forall  (x : t1) (y : t1), le x y ∨ le y x.
Axiom t2 : Type.
Axiom t2_inhabited : Inhabited t2.
Global Existing Instance t2_inhabited.
Axiom t2_countable : Countable t2.
Global Existing Instance t2_countable.
Definition op (x : option t1) (y : option t1) : option t1 := match x with | None => y | Some a => (match y with | None => x | Some b => (if decide (lt b a) then y else x) end) end.
Axiom assoc : forall  (a : option t1) (b : option t1) (c : option t1), op a (op b c) = op (op a b) c.
Axiom neutral : forall  (x : option t1), op x None = x ∧ x = op None x.
Axiom agg : forall {α : Type} `{Inhabited α}, (α -> option t1) -> list α -> option t1.
Axiom agg'def : forall  {α : Type} `{Inhabited α} (s : list α) (f : α -> option t1), if decide (Z.of_nat (length s) = 0%Z) then agg f s = None else agg f s = op (f (nth 0%nat s inhabitant)) (agg f (drop 1%nat s)).
Definition measure {α : Type} `{Inhabited α} (d : t α) : option t1 := Some (key d).
Axiom selector : Type.
Axiom selector_inhabited : Inhabited selector.
Global Existing Instance selector_inhabited.
Axiom selector_countable : Countable selector.
Global Existing Instance selector_countable.
Definition selection_possible {ε : Type} {η : Type} `{Inhabited ε} `{Inhabited η} (x : ε) (s : list η) := ¬ Z.of_nat (length s) = 0%Z.
Definition lower_bound {α : Type} `{Inhabited α} (x : t1) (s : list (t α)) := ∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length s) -> le x (key (nth (Z.to_nat i) s inhabitant)).
Definition lower_bound_strict {α : Type} `{Inhabited α} (x : t1) (s : list (t α)) := ∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length s) -> lt x (key (nth (Z.to_nat i) s inhabitant)).
Definition selected {ε : Type} {α : Type} `{Inhabited ε} `{Inhabited α} (x : ε) (e : split (t α)) := match middle e with | None => False | Some d => lower_bound (key d) (right1 e) ∧ lower_bound_strict (key d) (left1 e) end.
Axiom measure_closure : forall {α : Type} `{Inhabited α}, t α -> option t1.
Axiom measure_closure_def : forall  {α : Type} `{Inhabited α} (y : t α), measure_closure y = measure y.
Theorem selected_part'vc {α : Type} `{Inhabited α} (d : t α) (rseq : list (t α)) (lseq : list (t α)) : let s : unit := () in let kd : t1 := key d in (match agg measure_closure rseq with | None => (match agg measure_closure lseq with | None => True | Some x => True end) | Some x => (match agg measure_closure lseq with | None => True | Some x1 => True end) end) ∧ (∀(result : part_base unit), (match agg measure_closure rseq with | None => (match agg measure_closure lseq with | None => result = Here | Some x => (∃(o1 : Z), ((0%Z < o1) = lt x kd ∧ (o1 < 0%Z) = lt kd x ∧ (o1 = 0%Z) = eq kd x) ∧ (if decide (o1 < 0%Z) then result = Here else result = Left ())) end) | Some x => (match agg measure_closure lseq with | None => (∃(o1 : Z), ((0%Z < o1) = lt x kd ∧ (o1 < 0%Z) = lt kd x ∧ (o1 = 0%Z) = eq kd x) ∧ (if decide (o1 ≤ 0%Z) then result = Here else result = Right ())) | Some x1 => (∃(o1 : Z), ((0%Z < o1) = lt x kd ∧ (o1 < 0%Z) = lt kd x ∧ (o1 = 0%Z) = eq kd x) ∧ (if decide (o1 ≤ 0%Z) then ∃(o2 : Z), ((0%Z < o2) = lt kd x1 ∧ (o2 < 0%Z) = lt x1 kd ∧ (o2 = 0%Z) = eq x1 kd) ∧ (if decide (o2 ≤ 0%Z) then result = Left () else result = Here) else ∃(o2 : Z), ((0%Z < o2) = lt x x1 ∧ (o2 < 0%Z) = lt x1 x ∧ (o2 = 0%Z) = eq x1 x) ∧ (if decide (o2 ≤ 0%Z) then result = Left () else result = Right ()))) end) end) -> (match result with | Here => selected s (split'mk lseq (Some d) rseq) | Left rsl => selection_possible rsl lseq ∧ (∀(e : split (t α)), selected rsl e ∧ rebuild e = lseq -> selected s (right_extend e d rseq)) | Right rsr => selection_possible rsr rseq ∧ (∀(e : split (t α)), selected rsr e ∧ rebuild e = rseq -> selected s (left_extend lseq d e)) end)).
Admitted.
