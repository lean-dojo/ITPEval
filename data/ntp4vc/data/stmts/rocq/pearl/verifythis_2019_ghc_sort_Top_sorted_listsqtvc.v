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
Require Import Why3.exn.Exn.
Open Scope Z_scope.
Axiom Trans : forall  (x : Z) (y : Z) (z : Z) (fact0 : x < y) (fact1 : y < z), x < z.
Inductive sorted : list Z -> Prop :=
 | Sorted_Nil : sorted ([] : list Z)
 | Sorted_One (x : Z) : sorted (cons x ([] : list Z))
 | Sorted_Two (x : Z) (y : Z) (l : list Z) : x < y -> sorted (cons y l) -> sorted (cons x (cons y l)).
Axiom sorted_mem : forall  (l : list Z) (x : Z), ((∀(y : Z), y ∈ l -> x < y) ∧ sorted l) = sorted (cons x l).
Axiom sorted_append : forall  (l1 : list Z) (l2 : list Z), (sorted l1 ∧ sorted l2 ∧ (∀(x : Z) (y : Z), x ∈ l1 -> y ∈ l2 -> x < y)) = sorted (l1 ++ l2).
Axiom Trans1 : forall  (x : Z) (y : Z) (z : Z) (fact0 : x ≤ y) (fact1 : y ≤ z), x ≤ z.
Inductive sorted1 : list Z -> Prop :=
 | Sorted_Nil1 : sorted1 ([] : list Z)
 | Sorted_One1 (x : Z) : sorted1 (cons x ([] : list Z))
 | Sorted_Two1 (x : Z) (y : Z) (l : list Z) : x ≤ y -> sorted1 (cons y l) -> sorted1 (cons x (cons y l)).
Axiom sorted_mem1 : forall  (l : list Z) (x : Z), ((∀(y : Z), y ∈ l -> x ≤ y) ∧ sorted1 l) = sorted1 (cons x l).
Axiom sorted_append1 : forall  (l1 : list Z) (l2 : list Z), (sorted1 l1 ∧ sorted1 l2 ∧ (∀(x : Z) (y : Z), x ∈ l1 -> y ∈ l2 -> x ≤ y)) = sorted1 (l1 ++ l2).
Inductive sorted2 : list Z -> Prop :=
 | Sorted_Nil2 : sorted2 ([] : list Z)
 | Sorted_One2 (x : Z) : sorted2 (cons x ([] : list Z))
 | Sorted_Two2 (y : Z) (x : Z) (l : list Z) : y ≤ x -> sorted2 (cons y l) -> sorted2 (cons x (cons y l)).
Axiom sorted_mem2 : forall  (l : list Z) (x : Z), ((∀(y : Z), y ∈ l -> y ≤ x) ∧ sorted2 l) = sorted2 (cons x l).
Axiom sorted_append2 : forall  (l1 : list Z) (l2 : list Z), (sorted2 l1 ∧ sorted2 l2 ∧ (∀(x : Z) (y : Z), x ∈ l1 -> y ∈ l2 -> y ≤ x)) = sorted2 (l1 ++ l2).
Definition compat (s : list Z) (t : list Z) := match (s, t) with | (cons x _, cons y _) => x ≤ y | (_, _) => True end.
Axiom rev_append_sorted_incr : forall  (s : list Z) (t : list Z), sorted1 (rev_append s t) = (sorted2 s ∧ sorted1 t ∧ compat s t).
Axiom rev_append_sorted_decr : forall  (s : list Z) (t : list Z), sorted2 (rev_append s t) = (sorted1 s ∧ sorted2 t ∧ compat t s).
Definition eqb (b1 : bool) (b2 : bool) : bool := implb b1 b2 && implb b2 b1.
Axiom eqb'spec : forall  (b1 : bool) (b2 : bool), (eqb b1 b2 = true) = (b1 = b2).
Axiom list_seq : Type.
Axiom list_seq_inhabited : Inhabited list_seq.
Global Existing Instance list_seq_inhabited.
Axiom list_seq_countable : Countable list_seq.
Global Existing Instance list_seq_countable.
Axiom list : list_seq -> Datatypes.list Z.
Axiom seq : list_seq -> Datatypes.list Z.
Axiom list_seq'invariant : forall  (self : list_seq), seq self = rev (list self).
Definition list_seq'eq (a : list_seq) (b : list_seq) := list a = list b ∧ seq a = seq b.
Axiom list_seq'inj : forall  (a : list_seq) (b : list_seq) (fact0 : list_seq'eq a b), a = b.
Axiom nil : list_seq.
Axiom nil'def : list nil = ([] : Datatypes.list Z) ∧ seq nil = ([] : Datatypes.list Z).
Axiom order : Datatypes.list Z -> Datatypes.list Z.
Axiom order'def : forall  (l : Datatypes.list Z) (fact0 : sorted l ∨ sorted2 l), match l with | [] => order l = l | cons _ [] => order l = l | cons h1 (cons h2 _) => (if decide (h1 < h2) then order l = l else order l = rev l) end.
Axiom order'spec'0 : forall  (l : Datatypes.list Z) (fact0 : sorted l ∨ sorted2 l), sorted1 (order l).
Axiom order'spec : forall  (l : Datatypes.list Z) (fact0 : sorted l ∨ sorted2 l), l ≡ₚ order l.
Axiom infix_plpl_closure : forall {α : Type} `{Inhabited α}, Datatypes.list α -> Datatypes.list α -> Datatypes.list α.
Axiom infix_plpl_closure_def : forall  {α : Type} `{Inhabited α} (y : Datatypes.list α) (y1 : Datatypes.list α), infix_plpl_closure y y1 = y ++ y1.
Theorem sorted_lists'vc (cutp : list_seq) (s : Datatypes.list Z) (fact0 : 0%Z < Z.of_nat (length (list cutp))) (fact1 : ∀(x : Z) (y : Z), 0%Z ≤ x ∧ x < y ∧ y < Z.of_nat (length (seq cutp)) -> nth (Z.to_nat x) (seq cutp) inhabitant ≤ nth (Z.to_nat y) (seq cutp) inhabitant) (fact2 : ∀(z : Z), z ∈ list cutp -> 0%Z ≤ z ∧ z ≤ Z.of_nat (length s)) (fact3 : ∀(k : Z), 0%Z ≤ k ∧ k < Z.of_nat (length (seq cutp)) - 1%Z -> (let ck : Z := nth (Z.to_nat k) (seq cutp) inhabitant in let ck1 : Z := nth (Z.to_nat (k + 1%Z)) (seq cutp) inhabitant in (∀(z1 : Z) (z2 : Z), ck ≤ z1 ∧ z1 < z2 ∧ z2 < ck1 -> nth (Z.to_nat z1) s inhabitant < nth (Z.to_nat z2) s inhabitant) ∨ (∀(z1 : Z) (z2 : Z), ck ≤ z1 ∧ z1 < z2 ∧ z2 < ck1 -> nth (Z.to_nat z2) s inhabitant ≤ nth (Z.to_nat z1) s inhabitant))) : let ls : Datatypes.list Z := list cutp in let seq1 : Datatypes.list Z := seq cutp in (match ls with | [] => True | cons _ [] => True | cons h1 (cons h2 t) => ((0%Z ≤ h2 ∧ h2 ≤ Z.of_nat (length s)) ∧ (0%Z ≤ h1 ∧ h1 ≤ Z.of_nat (length s)) ∧ ((∀(z1 : Z) (z2 : Z), h2 ≤ z1 ∧ z1 < z2 ∧ z2 < h1 -> nth (Z.to_nat z1) s inhabitant < nth (Z.to_nat z2) s inhabitant) ∨ (∀(z1 : Z) (z2 : Z), h2 ≤ z1 ∧ z1 < z2 ∧ z2 < h1 -> nth (Z.to_nat z2) s inhabitant ≤ nth (Z.to_nat z1) s inhabitant))) ∧ (∀(seqi : Datatypes.list Z), (∀(x : Z), count_occ' seqi x = map_occ_list x (nth_i s) h2 h1) ∧ (∀(x : Z), x ∈ seqi -> (∃(z : Z), (h2 ≤ z ∧ z < h1) ∧ nth (Z.to_nat z) s inhabitant = x)) ∧ ((∀(z1 : Z) (z2 : Z), h2 ≤ z1 ∧ z1 < z2 ∧ z2 < h1 -> nth (Z.to_nat z1) s inhabitant < nth (Z.to_nat z2) s inhabitant) -> sorted seqi) ∧ ((∀(z1 : Z) (z2 : Z), h2 ≤ z1 ∧ z1 < z2 ∧ z2 < h1 -> nth (Z.to_nat z2) s inhabitant ≤ nth (Z.to_nat z1) s inhabitant) -> sorted2 seqi) ∧ (sorted seqi ∨ sorted2 seqi) -> (let o1 : Z := Z.of_nat (length seq1) - 1%Z in (0%Z ≤ 0%Z ∧ 0%Z ≤ o1 ∧ o1 ≤ Z.of_nat (length seq1)) ∧ (let o2 : Datatypes.list Z := drop 0%nat (take (Z.to_nat o1 - 0%nat) seq1) in Z.of_nat (length o2) = o1 - 0%Z ∧ (∀(k : Z), 0%Z ≤ k ∧ k < o1 - 0%Z -> nth (Z.to_nat k) o2 inhabitant = nth (Z.to_nat (0%Z + k)) seq1 inhabitant) -> (let o3 : Datatypes.list Z := cons h2 t in o2 = rev o3 ∧ (∀(lseq : list_seq), list lseq = o3 ∧ seq lseq = o2 -> ((match list cutp with | [] => False | cons _ f => f = list lseq end) ∧ 0%Z < Z.of_nat (length (list lseq)) ∧ (∀(x : Z) (y : Z), 0%Z ≤ x ∧ x < y ∧ y < Z.of_nat (length (seq lseq)) -> nth (Z.to_nat x) (seq lseq) inhabitant ≤ nth (Z.to_nat y) (seq lseq) inhabitant) ∧ (∀(z : Z), z ∈ list lseq -> 0%Z ≤ z ∧ z ≤ Z.of_nat (length s)) ∧ (∀(k : Z), 0%Z ≤ k ∧ k < Z.of_nat (length (seq lseq)) - 1%Z -> (let ck : Z := nth (Z.to_nat k) (seq lseq) inhabitant in let ck1 : Z := nth (Z.to_nat (k + 1%Z)) (seq lseq) inhabitant in (∀(z1 : Z) (z2 : Z), ck ≤ z1 ∧ z1 < z2 ∧ z2 < ck1 -> nth (Z.to_nat z1) s inhabitant < nth (Z.to_nat z2) s inhabitant) ∨ (∀(z1 : Z) (z2 : Z), ck ≤ z1 ∧ z1 < z2 ∧ z2 < ck1 -> nth (Z.to_nat z2) s inhabitant ≤ nth (Z.to_nat z1) s inhabitant)))) ∧ (∀(o4 : Datatypes.list (Datatypes.list Z)), (∀(l : Datatypes.list Z), l ∈ o4 -> sorted1 l) ∧ (∀(x : Z), count_occ' (foldr' infix_plpl_closure o4 ([] : Datatypes.list Z)) x = map_occ_list x (nth_i s) (nth 0%nat (seq lseq) inhabitant) (nth (Z.to_nat (Z.of_nat (length (seq lseq)) - 1%Z)) (seq lseq) inhabitant)) -> sorted seqi ∨ sorted2 seqi)))))) end) ∧ (∀(result : Datatypes.list (Datatypes.list Z)), (match ls with | [] => result = ([] : Datatypes.list (Datatypes.list Z)) | cons _ [] => result = ([] : Datatypes.list (Datatypes.list Z)) | cons h1 (cons h2 t) => (∃(seqi : Datatypes.list Z), ((∀(x : Z), count_occ' seqi x = map_occ_list x (nth_i s) h2 h1) ∧ (∀(x : Z), x ∈ seqi -> (∃(z : Z), (h2 ≤ z ∧ z < h1) ∧ nth (Z.to_nat z) s inhabitant = x)) ∧ ((∀(z1 : Z) (z2 : Z), h2 ≤ z1 ∧ z1 < z2 ∧ z2 < h1 -> nth (Z.to_nat z1) s inhabitant < nth (Z.to_nat z2) s inhabitant) -> sorted seqi) ∧ ((∀(z1 : Z) (z2 : Z), h2 ≤ z1 ∧ z1 < z2 ∧ z2 < h1 -> nth (Z.to_nat z2) s inhabitant ≤ nth (Z.to_nat z1) s inhabitant) -> sorted2 seqi) ∧ (sorted seqi ∨ sorted2 seqi)) ∧ (let o1 : Z := Z.of_nat (length seq1) - 1%Z in let o2 : Datatypes.list Z := drop 0%nat (take (Z.to_nat o1 - 0%nat) seq1) in (Z.of_nat (length o2) = o1 - 0%Z ∧ (∀(k : Z), 0%Z ≤ k ∧ k < o1 - 0%Z -> nth (Z.to_nat k) o2 inhabitant = nth (Z.to_nat (0%Z + k)) seq1 inhabitant)) ∧ (∃(lseq : list_seq), (list lseq = cons h2 t ∧ seq lseq = o2) ∧ (∃(o3 : Datatypes.list (Datatypes.list Z)), ((∀(l : Datatypes.list Z), l ∈ o3 -> sorted1 l) ∧ (∀(x : Z), count_occ' (foldr' infix_plpl_closure o3 ([] : Datatypes.list Z)) x = map_occ_list x (nth_i s) (nth 0%nat (seq lseq) inhabitant) (nth (Z.to_nat (Z.of_nat (length (seq lseq)) - 1%Z)) (seq lseq) inhabitant))) ∧ (let o4 : Datatypes.list Z := order seqi in (sorted1 o4 ∧ seqi ≡ₚ o4) ∧ result = cons o4 o3))))) end) -> (∀(l : Datatypes.list Z), l ∈ result -> sorted1 l) ∧ (∀(x : Z), count_occ' (foldr' infix_plpl_closure result ([] : Datatypes.list Z)) x = map_occ_list x (nth_i s) (nth 0%nat (seq cutp) inhabitant) (nth (Z.to_nat (Z.of_nat (length (seq cutp)) - 1%Z)) (seq cutp) inhabitant))).
Admitted.
