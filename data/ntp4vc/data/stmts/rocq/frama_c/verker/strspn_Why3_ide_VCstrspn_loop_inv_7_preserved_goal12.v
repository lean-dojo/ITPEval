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
Require Import verker.A_StrSpn.A_StrSpn.
Require Import verker.Compound.Compound.
Require Import verker.A_Strlen.A_Strlen.
Require Import Why3.Cint.Cint.
Open Scope Z_scope.
Theorem goal12 (t_1 : addr -> Z) (a_1 : addr) (a_3 : addr) (a : addr) (a_2 : addr) (t : Z -> Z) : let x : Z := t_1 a_1 in let x_1 : Z := t_1 a_3 in let x_2 : Z := offset a_1 in let x_3 : Z := offset a in let x_4 : Z := l_strlen t_1 a in let a_4 : addr := shift a_2 (l_strlen t_1 a_2) in let a_5 : addr := shift a_3 1%Z in ¬ x = 0%Z -> ¬ x_1 = 0%Z -> ¬ x_1 = x -> x_2 + l_strspn a_1 a_2 = x_3 + l_strspn a a_2 -> x_3 ≤ x_2 -> region (base a) ≤ 0%Z -> region (base a_2) ≤ 0%Z -> x_2 ≤ x_3 + x_4 -> linked t -> sconst t_1 -> addr_le a a_1 -> addr_le a_2 a_3 -> is_sint8 x -> is_sint8 x_1 -> p_valid_str t t_1 a -> p_valid_str t t_1 a_1 -> p_valid_str t t_1 a_2 -> p_valid_str t t_1 a_3 -> is_uint64 (x_2 - x_3) -> addr_le a_1 (shift a x_4) -> addr_le a_3 a_4 -> (p_in_array t_1 a_2 x -> p_in_array t_1 a_3 x) -> (∀(a_6 : addr), addr_lt a_6 a_3 -> addr_le a_2 a_6 -> ¬ x = t_1 a_6) -> (∀(a_6 : addr), addr_lt a_6 a_1 -> addr_le a a_6 -> (∃(a_7 : addr), t_1 a_6 = t_1 a_7 ∧ addr_le a_2 a_7 ∧ addr_lt a_7 a_4)) -> addr_le a_2 a_5 ∧ addr_le a_5 a_4.
Admitted.
