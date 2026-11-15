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
Theorem goal0 (a_1 : addr) (a : addr) (t_1 : addr -> Z) (a_2 : addr) (a_3 : addr) (i : Z) (t : Z -> Z) (a_5 : addr) (a_4 : addr) : let x : Z := offset a_1 in let x_1 : Z := offset a in let x_2 : Z := l_strlen t_1 a in let x_3 : Z := t_1 a_1 in let x_4 : Z := t_1 a_2 in let a_6 : addr := shift a_3 (l_strlen t_1 a_3) in let x_5 : Z := i + x_1 in x + l_strspn a_1 a_3 = x_1 + l_strspn a a_3 -> x_1 ≤ x -> region (base a) ≤ 0%Z -> region (base a_3) ≤ 0%Z -> x ≤ x_1 + x_2 -> linked t -> sconst t_1 -> is_uint64 i -> addr_le a a_1 -> addr_le a_3 a_5 -> is_sint8 x_3 -> is_sint8 x_4 -> p_valid_str t t_1 a -> p_valid_str t t_1 a_1 -> p_valid_str t t_1 a_3 -> is_uint64 (x - x_1) -> addr_lt a_5 a_6 -> addr_le a_1 (shift a x_2) -> (if decide (x_3 = 0%Z) then x_5 = x else a_2 = a_1 ∧ t_1 a_4 = 0%Z ∧ x_5 = offset a_2 ∧ addr_le a_3 a_4 ∧ p_valid_str t t_1 a_4 ∧ ¬ p_in_array t_1 a_3 x_4 ∧ addr_le a_4 a_6 ∧ (∀(a_7 : addr), addr_lt a_7 a_4 -> addr_le a_3 a_7 -> ¬ x_4 = t_1 a_7)) -> (∀(a_7 : addr), addr_lt a_7 a_1 -> addr_le a a_7 -> (∃(a_8 : addr), t_1 a_7 = t_1 a_8 ∧ addr_le a_3 a_8 ∧ addr_lt a_8 a_6)) -> ¬ t_1 (shift a i) = t_1 a_5.
Admitted.
