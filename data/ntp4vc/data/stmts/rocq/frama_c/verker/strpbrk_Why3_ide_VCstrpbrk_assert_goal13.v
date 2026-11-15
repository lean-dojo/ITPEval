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
Require Import verker.A_StrPBrk.A_StrPBrk.
Require Import verker.A_StrSpn.A_StrSpn.
Require Import verker.Compound.Compound.
Require Import verker.A_Strlen.A_Strlen.
Require Import Why3.Cint.Cint.
Open Scope Z_scope.
Theorem goal13 (t_1 : addr -> Z) (a : addr) (a_1 : addr) (a_2 : addr) (a_3 : addr) (t : Z -> Z) : let x : Z := t_1 a in let x_1 : Z := t_1 a_1 in let a_4 : addr := shift a_2 (l_strlen t_1 a_2) in let a_5 : addr := shift a_3 (l_strlen t_1 a_3) in ¬ x = 0%Z -> ¬ x_1 = 0%Z -> x_1 = x -> l_strpbrk a_3 a_2 = l_strpbrk a_1 a_2 -> region (base a_2) ≤ 0%Z -> region (base a_3) ≤ 0%Z -> linked t -> sconst t_1 -> addr_le a_2 a -> addr_le a_3 a_1 -> is_sint8 x -> is_sint8 x_1 -> p_valid_str t t_1 a -> p_valid_str t t_1 a_1 -> p_valid_str t t_1 a_2 -> p_valid_str t t_1 a_3 -> addr_le a a_4 -> addr_le a_1 a_5 -> (p_in_array t_1 a_2 x_1 -> p_in_array t_1 a x_1) -> (∀(a_6 : addr), addr_lt a_6 a -> addr_le a_2 a_6 -> ¬ x_1 = t_1 a_6) -> (∀(a_7 : addr) (a_6 : addr), addr_lt a_7 a_1 -> addr_le a_2 a_6 -> addr_le a_3 a_7 -> addr_lt a_6 a_4 -> ¬ t_1 a_7 = t_1 a_6) -> addr_lt a a_4 ∧ addr_lt a_1 a_5.
Admitted.
