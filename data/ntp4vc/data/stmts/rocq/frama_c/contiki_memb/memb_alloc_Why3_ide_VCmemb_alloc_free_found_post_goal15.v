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
Require Import Why3.Qed.Qed.
Require Import contiki_memb.Axiomatic13.Axiomatic13.
Require Import Why3.Memory.Memory.
Require Import contiki_memb.Compound.Compound.
Require Import contiki_memb.A_OccArray.A_OccArray.
Require Import Why3.Cint.Cint.
Open Scope Z_scope.
Theorem goal15 (a_1 : addr) (t_4 : addr -> addr) (t_1 : addr -> Z) (i_2 : Z) (t_3 : addr -> Z) (i : Z) (i_1 : Z) (t : Z -> Z) (t_2 : addr -> Z) (a : addr) : let a_2 : addr := shift a_1 2%Z in let a_3 : addr := t_4 a_2 in let a_4 : addr := shift a_1 1%Z in let x : Z := t_1 a_4 in let a_5 : addr := shift a_1 0%Z in let x_1 : Z := t_1 a_5 in let a_6 : addr := shift a_3 i_2 in let a_7 : addr := shift a_1 3%Z in let a_8 : addr := t_4 a_7 in let x_2 : Z := i_2 * x_1 in t_3 (shift a_3 i) = 0%Z -> 0%Z ≤ i -> 0%Z ≤ i_1 -> i < x -> i_1 ≤ x -> region (base a_1) ≤ 0%Z -> framed t_4 -> linked t -> sconst t_3 -> is_sint32 i_1 -> is_sint32 i_2 -> is_uint16 x -> is_uint16 x_1 -> p_valid_memb t t_4 t_1 a_1 -> valid_rd t a_4 1%Z -> (if decide (i_1 < x) then i_2 = i_1 ∧ t_3 a_6 = 0%Z ∧ fun_updt t_3 a_6 1%Z = t_2 ∧ shift a_8 x_2 = a ∧ - 2147483648%Z ≤ x_2 ∧ x_2 ≤ 2147483647%Z ∧ valid_rd t a_2 1%Z ∧ valid_rd t a_7 1%Z ∧ valid_rd t a_5 1%Z ∧ valid_rd t a_6 1%Z ∧ valid_rw t a_6 1%Z else t_3 = t_2 ∧ Mk_addr 0%Z 0%Z = a) -> (∀(i_3 : Z), 0%Z ≤ i_3 -> i_3 < i_1 -> ¬ t_3 (shift a_3 i_3) = 0%Z) -> (∃(i_3 : Z), let a_9 : addr := shift a_3 i_3 in t_2 a_9 = 1%Z ∧ t_3 a_9 = 0%Z ∧ shift a_8 (i_3 * x_1) = a ∧ 0%Z ≤ i_3 ∧ i_3 < x ∧ (∀(i_4 : Z), let a_10 : addr := shift a_3 i_4 in 0%Z ≤ i_4 ∧ i_4 < i_3 ∨ i_3 < i_4 ∧ i_4 < x -> t_3 a_10 = t_2 a_10)).
Admitted.
