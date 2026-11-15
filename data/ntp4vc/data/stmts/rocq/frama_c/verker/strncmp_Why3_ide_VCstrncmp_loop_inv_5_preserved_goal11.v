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
Require Import verker.Axiomatic3.Axiomatic3.
Require Import Why3.Memory.Memory.
Require Import Why3.Cint.Cint.
Require Import verker.A_Strnlen.A_Strnlen.
Require Import verker.Compound.Compound.
Require Import verker.A_Strlen.A_Strlen.
Open Scope Z_scope.
Theorem goal11 (t_1 : addr -> Z) (a_1 : addr) (a_3 : addr) (a : addr) (i : Z) (a_2 : addr) (t : Z -> Z) : let x : Z := t_1 a_1 in let x_1 : Z := to_uint8 x in let x_2 : Z := t_1 a_3 in let x_3 : Z := offset a in let x_4 : Z := i + x_3 in let x_5 : Z := offset a_1 in let x_6 : Z := offset a_2 in let x_7 : Z := offset a_3 in let x_8 : Z := x_7 - x_6 in let x_9 : Z := t_1 (shift a_2 x_8) in let x_10 : Z := t_1 (shift a x_8) in let x_12 : Z := i + x_3 - x_5 in let x_13 : Z := l_strnlen t_1 a i in let x_14 : Z := l_strnlen t_1 a_2 i in let x_15 : Z := to_uint64 (i + x_3 - 1%Z - x_5) in ¬ x_1 = 0%Z -> to_uint8 x_2 = x_1 -> ¬ x_4 = x_5 -> x_5 + x_6 = x_3 + x_7 -> x_9 = x_10 -> x_5 + l_strnlen t_1 a_1 x_12 = x_3 + x_13 -> x_7 + l_strnlen t_1 a_3 x_12 = x_6 + x_14 -> x_3 ≤ x_5 -> region (base a) ≤ 0%Z -> region (base a_2) ≤ 0%Z -> x_5 ≤ x_4 -> linked t -> sconst t_1 -> is_uint64 i -> addr_le a a_1 -> addr_le a_2 a_3 -> is_sint8 x -> is_sint8 x_2 -> p_valid_strn t t_1 a i -> p_valid_strn t t_1 a_2 i -> is_uint64 x_12 -> addr_le a_1 (shift a x_13) -> addr_le a_3 (shift a_2 x_14) -> is_sint8 x_10 -> is_sint8 x_9 -> p_valid_strn t t_1 a_1 x_12 -> p_valid_strn t t_1 a_3 x_12 -> (∀(i_1 : Z), 0%Z ≤ i_1 -> i_1 + x_3 < x_5 -> t_1 (shift a_2 i_1) = t_1 (shift a i_1)) -> (∀(i_1 : Z), let x_16 : Z := t_1 (shift a_2 i_1) in let x_17 : Z := t_1 (shift a i_1) in 0%Z ≤ i_1 -> i_1 < x_14 -> (to_uint8 x_16 = to_uint8 x_17) = (x_16 = x_17)) -> p_valid_strn t t_1 (shift a_1 1%Z) x_15 ∧ p_valid_strn t t_1 (shift a_3 1%Z) x_15.
Admitted.
