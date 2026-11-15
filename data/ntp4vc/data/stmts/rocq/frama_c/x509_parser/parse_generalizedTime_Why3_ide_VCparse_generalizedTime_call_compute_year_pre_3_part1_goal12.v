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
Theorem goal12 (a_7 : addr) (t_1 : addr -> Z) (a_1 : addr) (a : addr) (a_2 : addr) (a_3 : addr) (a_4 : addr) (a_5 : addr) (a_6 : addr) (i : Z) (i_1 : Z) (t : Z -> Z) : let a_8 : addr := shift a_7 0%Z in let a_9 : addr := shift a_7 1%Z in let a_10 : addr := shift a_7 16%Z in let a_11 : addr := shift a_7 2%Z in let a_12 : addr := shift a_7 3%Z in let a_13 : addr := shift a_7 4%Z in let x : Z := t_1 a_13 in let a_14 : addr := shift a_7 5%Z in ¬ a_1 = a -> ¬ a_2 = a -> ¬ a_2 = a_1 -> ¬ a_3 = a -> ¬ a_3 = a_1 -> ¬ a_3 = a_2 -> ¬ a_4 = a -> ¬ a_4 = a_1 -> ¬ a_4 = a_2 -> ¬ a_4 = a_3 -> ¬ a_5 = a -> ¬ a_5 = a_1 -> ¬ a_5 = a_2 -> ¬ a_5 = a_3 -> ¬ a_5 = a_4 -> ¬ a_6 = a -> ¬ a_6 = a_1 -> ¬ a_6 = a_2 -> ¬ a_6 = a_3 -> ¬ a_6 = a_4 -> ¬ a_6 = a_5 -> ¬ Mk_addr 0%Z 0%Z = a_7 -> t_1 a_8 = 24%Z -> t_1 a_9 = 15%Z -> t_1 a_10 = 90%Z -> 0%Z ≤ i -> region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> region (base a_2) ≤ 0%Z -> region (base a_3) ≤ 0%Z -> region (base a_4) ≤ 0%Z -> region (base a_5) ≤ 0%Z -> region (base a_6) ≤ 0%Z -> region (base a_7) ≤ 0%Z -> 14%Z ≤ i_1 -> 17%Z ≤ i -> linked t -> is_uint8 i_1 -> is_uint16 i -> valid_rw t a 1%Z -> valid_rw t a_1 1%Z -> valid_rw t a_2 1%Z -> valid_rw t a_3 1%Z -> valid_rw t a_4 1%Z -> valid_rw t a_5 1%Z -> valid_rw t a_6 1%Z -> is_uint8 (t_1 a_11) -> is_uint8 (t_1 a_12) -> is_uint8 x -> is_uint8 (t_1 a_14) -> valid_rd t a_8 1%Z -> valid_rd t a_9 1%Z -> valid_rd t a_11 1%Z -> valid_rd t a_12 1%Z -> valid_rd t a_13 1%Z -> valid_rd t a_14 1%Z -> valid_rd t a_10 1%Z -> separated a 1%Z a_8 i -> separated a_1 1%Z a_8 i -> separated a_2 1%Z a_8 i -> separated a_3 1%Z a_8 i -> separated a_4 1%Z a_8 i -> separated a_5 1%Z a_8 i -> separated a_6 1%Z a_8 i -> valid_rd t (shift a_7 (2%Z + i_1)) 1%Z -> (0%Z < i -> valid_rd t a_8 i) -> (∀(i_2 : Z), let x_1 : Z := t_1 (shift a_7 (2%Z + i_2)) in 0%Z ≤ i_2 -> i_2 < i_1 -> 48%Z ≤ x_1 ∧ x_1 ≤ 57%Z) -> 48%Z ≤ x.
Admitted.
