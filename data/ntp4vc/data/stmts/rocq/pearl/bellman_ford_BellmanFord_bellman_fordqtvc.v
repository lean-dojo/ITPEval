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
Require Import Why3.int.IntInf.
Require Import Why3.map.Const.
Require Import bellman_ford_vcg.bellman_ford.Graph.
Open Scope Z_scope.
Axiom set : Type.
Axiom set_inhabited : Inhabited set.
Global Existing Instance set_inhabited.
Axiom set_countable : Countable set.
Global Existing Instance set_countable.
Axiom to_fset : set -> gset (vertex * vertex).
Axiom choose1 : set -> vertex * vertex.
Axiom choose'spec : forall  (s : set) (fact0 : ¬ to_fset s = ∅), choose1 s ∈ to_fset s.
Axiom t : Type -> Type.
Axiom t_inhabited : forall  {α : Type} `{Inhabited α} `{Countable α}, Inhabited (t α).
Global Existing Instance t_inhabited.
Axiom contents : forall {α : Type} `{Inhabited α} `{Countable α}, t α -> vertex -> α.
Axiom create : forall {α : Type} `{Inhabited α} `{Countable α}, α -> t α.
Axiom create'spec : forall  {α : Type} `{Inhabited α} `{Countable α} (x : α), contents (create x) = (const : α -> vertex -> α) x.
Axiom mixfix_lbrb : forall {α : Type} `{Inhabited α} `{Countable α}, t α -> vertex -> α.
Axiom mixfix_lbrb'spec : forall  {α : Type} `{Inhabited α} `{Countable α} (m : t α) (k : vertex), mixfix_lbrb m k = contents m k.
Axiom mixfix_lblsmnrb : forall {α : Type} `{Inhabited α} `{Countable α}, t α -> vertex -> α -> t α.
Axiom mixfix_lblsmnrb'spec : forall  {α : Type} `{Inhabited α} `{Countable α} (m : t α) (k : vertex) (v : α), contents (mixfix_lblsmnrb m k v) = fun_updt (contents m) k v.
Axiom distmap : Type.
Axiom distmap_inhabited : Inhabited distmap.
Global Existing Instance distmap_inhabited.
Axiom distmap_countable : Countable distmap.
Global Existing Instance distmap_countable.
Definition inv1 (m : t IntInf.t) (pass : Z) (via : gset (vertex * vertex)) := ∀(v : vertex), v ∈ vertices -> (match mixfix_lbrb m v with | Finite n => (∃(l : list vertex), path s l v ∧ path_weight l v = n) ∧ (∀(l : list vertex), path s l v -> Z.of_nat (length l) < pass -> n ≤ path_weight l v) ∧ (∀(u : vertex) (l : list vertex), path s l u -> Z.of_nat (length l) < pass -> (u, v) ∈ via -> n ≤ path_weight l u + weight u v) | Infinite => (∀(l : list vertex), path s l v -> pass ≤ Z.of_nat (length l)) ∧ (∀(u : vertex), (u, v) ∈ via -> (∀(lu : list vertex), path s lu u -> pass ≤ Z.of_nat (length lu))) end).
Definition inv2 (m : t IntInf.t) (via : gset (vertex * vertex)) := ∀(u : vertex) (v : vertex), (u, v) ∈ via -> le (mixfix_lbrb m v) (add (mixfix_lbrb m u) (Finite (weight u v))).
Theorem bellman_ford'vc : let m : t IntInf.t := mixfix_lblsmnrb (create Infinite) s (Finite 0%Z) in let o1 : Z := Z.of_nat (size vertices) - 1%Z in (1%Z ≤ o1 + 1%Z -> inv1 m 1%Z (∅ : gset (vertex * vertex)) ∧ (∀(m1 : t IntInf.t), (∀(i : Z), (1%Z ≤ i ∧ i ≤ o1) ∧ inv1 m1 i (∅ : gset (vertex * vertex)) -> (∀(es : set), to_fset es = edges -> (to_fset es ⊆ edges ∧ inv1 m1 i (edges ∖ to_fset es)) ∧ (∀(es1 : set) (m2 : t IntInf.t), to_fset es1 ⊆ edges ∧ inv1 m2 i (edges ∖ to_fset es1) -> (if decide (¬ to_fset es1 = ∅) then let via : gset (vertex * vertex) := edges ∖ to_fset es1 in ¬ to_fset es1 = ∅ ∧ (∀(es2 : set), let o2 : vertex * vertex := choose1 es1 in o2 ∈ to_fset es1 ∧ to_fset es2 = remove_set o2 (to_fset es1) -> (match o2 with | (u, v) => ((1%Z ≤ i ∧ (u, v) ∈ edges ∧ ¬ (u, v) ∈ via) ∧ inv1 m2 i via) ∧ (∀(m3 : t IntInf.t), inv1 m3 i (insert_set (u, v) via) -> (0%Z ≤ Z.of_nat (size (to_fset es1)) ∧ Z.of_nat (size (to_fset es2)) < Z.of_nat (size (to_fset es1))) ∧ to_fset es2 ⊆ edges ∧ inv1 m3 i (edges ∖ to_fset es2)) end)) else inv1 m2 (i + 1%Z) (∅ : gset (vertex * vertex)))))) ∧ (inv1 m1 (o1 + 1%Z) (∅ : gset (vertex * vertex)) -> (∀(es : set), to_fset es = edges -> (to_fset es ⊆ edges ∧ inv2 m1 (edges ∖ to_fset es)) ∧ (∀(es1 : set), to_fset es1 ⊆ edges ∧ inv2 m1 (edges ∖ to_fset es1) -> (if decide (¬ to_fset es1 = ∅) then ¬ to_fset es1 = ∅ ∧ (∀(es2 : set), let o2 : vertex * vertex := choose1 es1 in o2 ∈ to_fset es1 ∧ to_fset es2 = remove_set o2 (to_fset es1) -> (match o2 with | (u, v) => (let o3 : IntInf.t := mixfix_lbrb m1 v in o3 = contents m1 v -> (let o4 : IntInf.t := mixfix_lbrb m1 u in o4 = contents m1 u -> (if decide (lt (add o4 (Finite (weight u v))) o3) then ∃(v1 : vertex), negative_cycle v1 else (0%Z ≤ Z.of_nat (size (to_fset es1)) ∧ Z.of_nat (size (to_fset es2)) < Z.of_nat (size (to_fset es1))) ∧ to_fset es2 ⊆ edges ∧ inv2 m1 (edges ∖ to_fset es2)))) end)) else ∀(v : vertex), v ∈ vertices -> (match mixfix_lbrb m1 v with | Finite n => (∃(l : list vertex), path s l v ∧ path_weight l v = n) ∧ (∀(l : list vertex), path s l v -> n ≤ path_weight l v) | Infinite => (∀(l : list vertex), ¬ path s l v) end))))))) ∧ (o1 + 1%Z < 1%Z -> (∀(es : set), to_fset es = edges -> (to_fset es ⊆ edges ∧ inv2 m (edges ∖ to_fset es)) ∧ (∀(es1 : set), to_fset es1 ⊆ edges ∧ inv2 m (edges ∖ to_fset es1) -> (if decide (¬ to_fset es1 = ∅) then ¬ to_fset es1 = ∅ ∧ (∀(es2 : set), let o2 : vertex * vertex := choose1 es1 in o2 ∈ to_fset es1 ∧ to_fset es2 = remove_set o2 (to_fset es1) -> (match o2 with | (u, v) => (let o3 : IntInf.t := mixfix_lbrb m v in o3 = contents m v -> (let o4 : IntInf.t := mixfix_lbrb m u in o4 = contents m u -> (if decide (lt (add o4 (Finite (weight u v))) o3) then ∃(v1 : vertex), negative_cycle v1 else (0%Z ≤ Z.of_nat (size (to_fset es1)) ∧ Z.of_nat (size (to_fset es2)) < Z.of_nat (size (to_fset es1))) ∧ to_fset es2 ⊆ edges ∧ inv2 m (edges ∖ to_fset es2)))) end)) else ∀(v : vertex), v ∈ vertices -> (match mixfix_lbrb m v with | Finite n => (∃(l : list vertex), path s l v ∧ path_weight l v = n) ∧ (∀(l : list vertex), path s l v -> n ≤ path_weight l v) | Infinite => (∀(l : list vertex), ¬ path s l v) end))))).
Admitted.
