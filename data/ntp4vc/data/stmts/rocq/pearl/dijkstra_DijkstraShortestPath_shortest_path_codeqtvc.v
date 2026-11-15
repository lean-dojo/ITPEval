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
Axiom vertex : Type.
Axiom vertex_inhabited : Inhabited vertex.
Global Existing Instance vertex_inhabited.
Axiom vertex_countable : Countable vertex.
Global Existing Instance vertex_countable.
Axiom set : Type.
Axiom set_inhabited : Inhabited set.
Global Existing Instance set_inhabited.
Axiom set_countable : Countable set.
Global Existing Instance set_countable.
Axiom to_fset : set -> gset vertex.
Axiom choose1 : set -> vertex.
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
Axiom v : gset vertex.
Axiom g_succ : vertex -> gset vertex.
Axiom g_succ'spec : forall  (x_x : vertex), g_succ x_x ⊆ v.
Axiom weight : vertex -> vertex -> Z.
Axiom weight'spec : forall  (x : vertex) (x_1 : vertex), 0%Z ≤ weight x x_1.
Definition min (m : vertex) (q : set) (d : t Z) := m ∈ to_fset q ∧ (∀(x : vertex), x ∈ to_fset q -> mixfix_lbrb d m ≤ mixfix_lbrb d x).
Inductive path : vertex -> vertex -> Z -> Prop :=
 | Path_nil (x : vertex) : path x x 0%Z
 | Path_cons (x : vertex) (y : vertex) (d : Z) (z : vertex) : path x y d -> z ∈ g_succ y -> path x z (d + weight y z).
Definition shortest_path (x : vertex) (y : vertex) (d : Z) := path x y d ∧ (∀(d' : Z), path x y d' -> d ≤ d').
Definition inv_src (src : vertex) (s : set) (q : set) := src ∈ to_fset s ∨ src ∈ to_fset q.
Definition inv (src : vertex) (s : set) (q : set) (d : t Z) := inv_src src s q ∧ mixfix_lbrb d src = 0%Z ∧ to_fset s ⊆ v ∧ to_fset q ⊆ v ∧ (∀(v1 : vertex), v1 ∈ to_fset q -> ¬ v1 ∈ to_fset s) ∧ (∀(v1 : vertex), v1 ∈ to_fset s -> shortest_path src v1 (mixfix_lbrb d v1)) ∧ (∀(v1 : vertex), v1 ∈ to_fset q -> path src v1 (mixfix_lbrb d v1)).
Definition inv_succ (x_src : vertex) (s : set) (q : set) (d : t Z) := ∀(x : vertex), x ∈ to_fset s -> (∀(y : vertex), y ∈ g_succ x -> (y ∈ to_fset s ∨ y ∈ to_fset q) ∧ mixfix_lbrb d y ≤ mixfix_lbrb d x + weight x y).
Definition inv_succ2 (x_src : vertex) (s : set) (q : set) (d : t Z) (u : vertex) (su : set) := ∀(x : vertex), x ∈ to_fset s -> (∀(y : vertex), y ∈ g_succ x -> ¬ x = u ∨ x = u ∧ ¬ y ∈ to_fset su -> (y ∈ to_fset s ∨ y ∈ to_fset q) ∧ mixfix_lbrb d y ≤ mixfix_lbrb d x + weight x y).
Theorem shortest_path_code'vc (src : vertex) (dst : vertex) (visited : set) (q : set) (d : t Z) (fact0 : src ∈ v) (fact1 : dst ∈ v) (fact2 : to_fset visited = ∅) (fact3 : to_fset q = ({[src]} : gset _)) : inv src visited q (mixfix_lblsmnrb d src 0%Z) ∧ inv_succ src visited q (mixfix_lblsmnrb d src 0%Z) ∧ (∀(m : vertex), min m q (mixfix_lblsmnrb d src 0%Z) -> (∀(x : vertex) (dx : Z), path src x dx -> dx < mixfix_lbrb (mixfix_lblsmnrb d src 0%Z) m -> x ∈ to_fset visited)) ∧ (∀(q1 : set) (d1 : t Z) (visited1 : set), inv src visited1 q1 d1 ∧ inv_succ src visited1 q1 d1 ∧ (∀(m : vertex), min m q1 d1 -> (∀(x : vertex) (dx : Z), path src x dx -> dx < mixfix_lbrb d1 m -> x ∈ to_fset visited1)) -> (if decide (¬ to_fset q1 = ∅) then ¬ to_fset q1 = ∅ ∧ (∀(q2 : set) (u : vertex), min u q1 d1 ∧ to_fset q2 = remove_set u (to_fset q1) -> (∀(visited2 : set), to_fset visited2 = insert_set u (to_fset visited1) ∧ (if decide (u ∈ to_fset visited1) then size (to_fset visited2) = size (to_fset visited1) else Z.of_nat (size (to_fset visited2)) = Z.of_nat (size (to_fset visited1)) + 1%Z) -> (∀(su : set), to_fset su = g_succ u -> (to_fset su ⊆ g_succ u ∧ inv src visited2 q2 d1 ∧ inv_succ2 src visited2 q2 d1 u su) ∧ (∀(su1 : set) (q3 : set) (d2 : t Z), to_fset su1 ⊆ g_succ u ∧ inv src visited2 q3 d2 ∧ inv_succ2 src visited2 q3 d2 u su1 -> (if decide (¬ to_fset su1 = ∅) then ¬ to_fset su1 = ∅ ∧ (∀(su2 : set), let v1 : vertex := choose1 su1 in v1 ∈ to_fset su1 ∧ to_fset su2 = remove_set v1 (to_fset su1) -> (∀(q4 : set) (d3 : t Z), v1 ∈ to_fset visited2 ∧ q4 = q3 ∧ d3 = d2 ∨ v1 ∈ to_fset q4 ∧ mixfix_lbrb d3 v1 ≤ mixfix_lbrb d3 u + weight u v1 ∧ q4 = q3 ∧ d3 = d2 ∨ v1 ∈ to_fset q4 ∧ mixfix_lbrb d2 u + weight u v1 < mixfix_lbrb d2 v1 ∧ q4 = q3 ∧ d3 = mixfix_lblsmnrb d2 v1 (mixfix_lbrb d2 u + weight u v1) ∨ ¬ v1 ∈ to_fset visited2 ∧ ¬ v1 ∈ to_fset q3 ∧ to_fset q4 = insert_set v1 (to_fset q3) ∧ d3 = mixfix_lblsmnrb d2 v1 (mixfix_lbrb d2 u + weight u v1) -> (0%Z ≤ Z.of_nat (size (to_fset su1)) ∧ Z.of_nat (size (to_fset su2)) < Z.of_nat (size (to_fset su1))) ∧ to_fset su2 ⊆ g_succ u ∧ inv src visited2 q4 d3 ∧ inv_succ2 src visited2 q4 d3 u su2)) else (0%Z ≤ Z.of_nat (size v) - Z.of_nat (size (to_fset visited1)) ∧ Z.of_nat (size v) - Z.of_nat (size (to_fset visited2)) < Z.of_nat (size v) - Z.of_nat (size (to_fset visited1))) ∧ inv src visited2 q3 d2 ∧ inv_succ src visited2 q3 d2 ∧ (∀(m : vertex), min m q3 d2 -> (∀(x : vertex) (dx : Z), path src x dx -> dx < mixfix_lbrb d2 m -> x ∈ to_fset visited2))))))) else (∀(v1 : vertex), v1 ∈ to_fset visited1 -> shortest_path src v1 (mixfix_lbrb d1 v1)) ∧ (∀(v1 : vertex), ¬ v1 ∈ to_fset visited1 -> (∀(dv : Z), ¬ path src v1 dv)))).
Admitted.
