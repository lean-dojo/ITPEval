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
Theorem goal15 (t_1 : addr -> Z) (a_1 : addr) (a : addr) (a_3 : addr) (t : Z -> Z) (a_2 : addr) : let x : Z := t_1 a_1 in let x_1 : Z := offset a_1 in let x_2 : Z := offset a in let x_3 : Z := l_strlen t_1 a in ¬ x = 0%Z -> x_1 + l_strspn a_1 a_3 = x_2 + l_strspn a a_3 -> x_2 ≤ x_1 -> region (base a) ≤ 0%Z -> region (base a_3) ≤ 0%Z -> x_1 ≤ x_2 + x_3 -> linked t -> sconst t_1 -> addr_lt a_2 a_3 -> addr_le a a_1 -> addr_le a_3 a_2 -> is_sint8 x -> p_valid_str t t_1 a -> p_valid_str t t_1 a_1 -> p_valid_str t t_1 a_3 -> is_uint64 (x_1 - x_2) -> addr_le a_1 (shift a x_3) -> (∀(a_4 : addr), addr_lt a_4 a_1 -> addr_le a a_4 -> (∃(a_5 : addr), t_1 a_4 = t_1 a_5 ∧ addr_le a_3 a_5 ∧ addr_lt a_5 (shift a_3 (l_strlen t_1 a_3)))) -> ¬ t_1 a_2 = x.
Admitted.
