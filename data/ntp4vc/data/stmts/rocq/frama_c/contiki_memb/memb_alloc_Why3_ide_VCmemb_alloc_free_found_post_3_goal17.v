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
Theorem goal17 (a : addr) (t_4 : addr -> addr) (t_1 : addr -> Z) (i_2 : Z) (t_2 : addr -> Z) (i : Z) (i_1 : Z) (t : Z -> Z) (t_3 : addr -> Z) : let a_1 : addr := shift a 2%Z in let a_2 : addr := t_4 a_1 in let a_3 : addr := shift a 1%Z in let x : Z := t_1 a_3 in let a_4 : addr := shift a 0%Z in let x_1 : Z := t_1 a_4 in let a_5 : addr := shift a_2 i_2 in let x_2 : Z := i_2 * x_1 in t_2 (shift a_2 i) = 0%Z -> 0%Z ≤ i -> 0%Z ≤ i_1 -> i < x -> i_1 ≤ x -> region (base a) ≤ 0%Z -> framed t_4 -> linked t -> sconst t_2 -> is_sint32 i_1 -> is_sint32 i_2 -> is_uint16 x -> is_uint16 x_1 -> p_valid_memb t t_4 t_1 a -> valid_rd t a_3 1%Z -> (if decide (i_1 < x) then i_2 = i_1 ∧ t_2 a_5 = 0%Z ∧ fun_updt t_2 a_5 1%Z = t_3 ∧ - 2147483648%Z ≤ x_2 ∧ x_2 ≤ 2147483647%Z ∧ valid_rd t a_1 1%Z ∧ valid_rd t (shift a 3%Z) 1%Z ∧ valid_rd t a_4 1%Z ∧ valid_rd t a_5 1%Z ∧ valid_rw t a_5 1%Z else t_3 = t_2) -> (∀(i_3 : Z), 0%Z ≤ i_3 -> i_3 < i_1 -> ¬ t_2 (shift a_2 i_3) = 0%Z) -> 1%Z + l__memb_numfree t_4 t_3 t_1 a = l__memb_numfree t_4 t_2 t_1 a.
Admitted.
