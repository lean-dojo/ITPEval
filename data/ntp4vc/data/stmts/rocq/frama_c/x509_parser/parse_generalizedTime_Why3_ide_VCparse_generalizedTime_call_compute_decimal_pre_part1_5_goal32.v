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
Require Import x509_parser.Compound.Compound.
Require Import Why3.Cint.Cint.
Open Scope Z_scope.
Theorem goal32 (a_7 : addr) (t_1 : addr -> Z) (a_1 : addr) (a : addr) (a_2 : addr) (a_3 : addr) (a_4 : addr) (a_5 : addr) (a_6 : addr) (i : Z) (i_2 : Z) (i_3 : Z) (i_4 : Z) (i_5 : Z) (i_6 : Z) (i_1 : Z) (t : Z -> Z) : let a_8 : addr := shift a_7 0%Z in let a_9 : addr := shift a_7 1%Z in let a_10 : addr := shift a_7 16%Z in let a_11 : addr := shift a_7 2%Z in let x : Z := t_1 a_11 in let a_12 : addr := shift a_7 3%Z in let x_1 : Z := t_1 a_12 in let a_13 : addr := shift a_7 4%Z in let x_2 : Z := t_1 a_13 in let a_14 : addr := shift a_7 5%Z in let x_3 : Z := t_1 a_14 in let a_15 : addr := shift a_7 6%Z in let x_4 : Z := t_1 a_15 in let a_16 : addr := shift a_7 7%Z in let x_5 : Z := t_1 a_16 in let a_17 : addr := shift a_7 8%Z in let x_6 : Z := t_1 a_17 in let a_18 : addr := shift a_7 9%Z in let x_7 : Z := t_1 a_18 in let a_19 : addr := shift a_7 10%Z in let x_8 : Z := t_1 a_19 in let a_20 : addr := shift a_7 11%Z in let x_9 : Z := t_1 a_20 in let a_21 : addr := shift a_7 12%Z in let x_10 : Z := t_1 a_21 in let a_22 : addr := shift a_7 13%Z in let x_11 : Z := t_1 a_22 in let a_23 : addr := shift a_7 14%Z in let x_12 : Z := t_1 a_23 in let a_24 : addr := shift a_7 15%Z in ¬ a_1 = a -> ¬ a_2 = a -> ¬ a_2 = a_1 -> ¬ a_3 = a -> ¬ a_3 = a_1 -> ¬ a_3 = a_2 -> ¬ a_4 = a -> ¬ a_4 = a_1 -> ¬ a_4 = a_2 -> ¬ a_4 = a_3 -> ¬ a_5 = a -> ¬ a_5 = a_1 -> ¬ a_5 = a_2 -> ¬ a_5 = a_3 -> ¬ a_5 = a_4 -> ¬ a_6 = a -> ¬ a_6 = a_1 -> ¬ a_6 = a_2 -> ¬ a_6 = a_3 -> ¬ a_6 = a_4 -> ¬ a_6 = a_5 -> ¬ Mk_addr 0%Z 0%Z = a_7 -> t_1 a_8 = 24%Z -> t_1 a_9 = 15%Z -> t_1 a_10 = 90%Z -> 0%Z ≤ i -> 0%Z ≤ i_2 -> 0%Z ≤ i_3 -> 0%Z ≤ i_4 -> 0%Z ≤ i_5 -> 0%Z ≤ i_6 -> region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> region (base a_2) ≤ 0%Z -> region (base a_3) ≤ 0%Z -> region (base a_4) ≤ 0%Z -> region (base a_5) ≤ 0%Z -> region (base a_6) ≤ 0%Z -> region (base a_7) ≤ 0%Z -> 14%Z ≤ i_1 -> 17%Z ≤ i -> i_3 ≤ 99%Z -> i_4 ≤ 99%Z -> i_5 ≤ 99%Z -> i_6 ≤ 99%Z -> i_2 ≤ 9999%Z -> 48%Z ≤ x -> 48%Z ≤ x_1 -> 48%Z ≤ x_2 -> 48%Z ≤ x_3 -> 48%Z ≤ x_4 -> 48%Z ≤ x_5 -> 48%Z ≤ x_6 -> 48%Z ≤ x_7 -> 48%Z ≤ x_8 -> 48%Z ≤ x_9 -> 48%Z ≤ x_10 -> 48%Z ≤ x_11 -> x ≤ 57%Z -> x_1 ≤ 57%Z -> x_2 ≤ 57%Z -> x_3 ≤ 57%Z -> x_4 ≤ 57%Z -> x_5 ≤ 57%Z -> x_6 ≤ 57%Z -> x_7 ≤ 57%Z -> x_8 ≤ 57%Z -> x_9 ≤ 57%Z -> x_10 ≤ 57%Z -> x_11 ≤ 57%Z -> linked t -> is_uint8 i_1 -> is_uint8 i_3 -> is_uint8 i_4 -> is_uint8 i_5 -> is_uint8 i_6 -> is_uint16 i -> is_uint16 i_2 -> valid_rw t a 1%Z -> valid_rw t a_1 1%Z -> valid_rw t a_2 1%Z -> valid_rw t a_3 1%Z -> valid_rw t a_4 1%Z -> valid_rw t a_5 1%Z -> valid_rw t a_6 1%Z -> is_uint8 x -> is_uint8 x_1 -> is_uint8 x_2 -> is_uint8 x_3 -> is_uint8 x_4 -> is_uint8 x_5 -> is_uint8 x_6 -> is_uint8 x_7 -> is_uint8 x_8 -> is_uint8 x_9 -> is_uint8 x_10 -> is_uint8 x_11 -> is_uint8 x_12 -> is_uint8 (t_1 a_24) -> valid_rd t a_8 1%Z -> valid_rd t a_9 1%Z -> valid_rd t a_11 1%Z -> valid_rd t a_12 1%Z -> valid_rd t a_13 1%Z -> valid_rd t a_14 1%Z -> valid_rd t a_15 1%Z -> valid_rd t a_16 1%Z -> valid_rd t a_17 1%Z -> valid_rd t a_18 1%Z -> valid_rd t a_19 1%Z -> valid_rd t a_20 1%Z -> valid_rd t a_21 1%Z -> valid_rd t a_22 1%Z -> valid_rd t a_23 1%Z -> valid_rd t a_24 1%Z -> valid_rd t a_10 1%Z -> separated a 1%Z a_8 i -> separated a_1 1%Z a_8 i -> separated a_2 1%Z a_8 i -> separated a_3 1%Z a_8 i -> separated a_4 1%Z a_8 i -> separated a_5 1%Z a_8 i -> separated a_6 1%Z a_8 i -> valid_rd t (shift a_7 (2%Z + i_1)) 1%Z -> (0%Z < i -> valid_rd t a_8 i) -> (∀(i_7 : Z), let x_13 : Z := t_1 (shift a_7 (2%Z + i_7)) in 0%Z ≤ i_7 -> i_7 < i_1 -> 48%Z ≤ x_13 ∧ x_13 ≤ 57%Z) -> 48%Z ≤ x_12.
Admitted.
