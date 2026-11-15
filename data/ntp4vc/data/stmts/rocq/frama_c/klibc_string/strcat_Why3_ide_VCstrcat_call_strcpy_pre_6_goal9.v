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
Require Import Why3.Memory.Memory.
Require Import klibc_string.A_Length.A_Length.
Require Import klibc_string.Axiomatic.Axiomatic.
Require Import klibc_string.Compound.Compound.
Require Import Why3.Cint.Cint.
Require Import klibc_string.Axiomatic1.Axiomatic1.
Open Scope Z_scope.
Theorem goal9 (a_2 : addr) (t_1 : addr -> Z) (a : addr) (a_1 : addr) (t : Z -> Z) (i : Z) (i_3 : Z) (i_1 : Z) (i_2 : Z) (i_4 : Z) : let x : Z := base a_2 in let x_1 : Z := t_1 a in let a_3 : addr := shift a_2 0%Z in let x_2 : Z := l_length t_1 a_1 in let x_3 : Z := l_length t_1 a_2 in let a_4 : addr := shift a_1 0%Z in let x_4 : Z := 1%Z + x_2 in region (base a_1) ≤ 0%Z -> region x ≤ 0%Z -> linked t -> sconst t_1 -> is_sint8 x_1 -> p_length_of_str_is t t_1 a_1 i -> p_length_of_str_is t t_1 a_1 i_3 -> p_length_of_str_is t t_1 a_2 i_1 -> p_length_of_str_is t t_1 a_2 i_2 -> p_length_of_str_is t t_1 a_2 i_4 -> valid_rw t a_3 (x_2 + x_3) -> separated a_3 (1%Z + x_3) a_4 x_4 -> ((∀(i_5 : Z), 0%Z ≤ i_5 -> i_5 < x_3 -> ¬ t_1 (shift a_2 i_5) = 0%Z) -> Mk_addr 0%Z 0%Z = a) -> ((∃(i_5 : Z), t_1 (shift a_2 i_5) = 0%Z ∧ 0%Z ≤ i_5 ∧ i_5 < x_3) -> x_1 = 0%Z) -> ((∃(i_5 : Z), t_1 (shift a_2 i_5) = 0%Z ∧ 0%Z ≤ i_5 ∧ i_5 < x_3) -> x = base a) -> ((∃(i_5 : Z), t_1 (shift a_2 i_5) = 0%Z ∧ 0%Z ≤ i_5 ∧ i_5 < x_3) -> p_exists_first_occurence_of_char t t_1 a_2 0%Z (offset a - offset a_2)) -> ((∃(i_5 : Z), t_1 (shift a_2 i_5) = 0%Z ∧ 0%Z ≤ i_5 ∧ i_5 < x_3) -> addr_le a_2 a ∧ addr_le a (shift a_2 x_3)) -> separated a_4 x_4 (shift a 0%Z) x_4.
Admitted.
