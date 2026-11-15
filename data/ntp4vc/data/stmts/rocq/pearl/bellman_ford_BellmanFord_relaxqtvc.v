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
Theorem relax'vc (pass : Z) (u : vertex) (v : vertex) (via : gset (vertex * vertex)) (m : t IntInf.t) (fact0 : 1%Z ≤ pass) (fact1 : (u, v) ∈ edges) (fact2 : ¬ (u, v) ∈ via) (fact3 : inv1 m pass via) : let o1 : IntInf.t := mixfix_lbrb m u in o1 = contents m u -> (let n : IntInf.t := add o1 (Finite (weight u v)) in let o2 : IntInf.t := mixfix_lbrb m v in o2 = contents m v -> (if decide (lt n o2) then inv1 (mixfix_lblsmnrb m v n) pass (insert_set (u, v) via) else inv1 m pass (insert_set (u, v) via))).
Admitted.
