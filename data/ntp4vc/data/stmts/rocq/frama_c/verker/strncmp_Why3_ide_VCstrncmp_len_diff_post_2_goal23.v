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
Theorem goal23 (a_1 : addr) (a_2 : addr) (a : addr) (a_3 : addr) (i_1 : Z) (t_1 : addr -> Z) (t : Z -> Z) (i_2 : Z) (i_3 : Z) (i : Z) : let x : Z := offset a_1 in let x_1 : Z := offset a_2 in let x_2 : Z := offset a in let x_3 : Z := offset a_3 in let x_4 : Z := i_1 + x - x_2 in let x_5 : Z := l_strnlen t_1 a_1 i_1 in let x_6 : Z := x + x_5 in let x_7 : Z := l_strnlen t_1 a_3 i_1 in let x_8 : Z := i_1 + x in x + x_1 = x_2 + x_3 -> x_2 + l_strnlen t_1 a x_4 = x_6 -> x_1 + l_strnlen t_1 a_2 x_4 = x_3 + x_7 -> 0%Z < i_1 -> x ≤ x_2 -> region (base a_1) ≤ 0%Z -> region (base a_3) ≤ 0%Z -> x_5 < x_7 -> x_2 ≤ x_8 -> linked t -> sconst t_1 -> is_uint8 i_2 -> is_uint8 i_3 -> is_sint32 i -> is_uint64 i_1 -> addr_le a_1 a -> addr_le a_3 a_2 -> p_valid_strn t t_1 a_1 i_1 -> p_valid_strn t t_1 a_3 i_1 -> is_uint64 x_4 -> addr_le a (shift a_1 x_5) -> addr_le a_2 (shift a_3 x_7) -> p_valid_strn t t_1 a x_4 -> p_valid_strn t t_1 a_2 x_4 -> (if decide (x_8 = x_2) then i = 0%Z else to_uint8 (t_1 a) = i_2 ∧ to_uint8 (t_1 a_2) = i_3 ∧ (if decide (i_3 = i_2) then i = 0%Z ∧ i_3 = 0%Z else if decide (i_3 < i_2) then i = - 1%Z else i = 1%Z) ∧ (i_2 = 0%Z -> x_5 = l_strlen t_1 a_1 ∧ x_6 = x_2 ∧ p_valid_str t t_1 a_1) ∧ (i_3 = 0%Z -> x_7 = l_strlen t_1 a_3 ∧ x + x_7 = x_2 ∧ p_valid_str t t_1 a_3)) -> (∀(i_4 : Z), 0%Z ≤ i_4 -> i_4 < x_7 -> t_1 (shift a_3 i_4) = t_1 (shift a_1 i_4)) -> (∀(i_4 : Z), 0%Z ≤ i_4 -> i_4 + x < x_2 -> t_1 (shift a_3 i_4) = t_1 (shift a_1 i_4)) -> (∀(i_4 : Z), let x_9 : Z := t_1 (shift a_3 i_4) in let x_10 : Z := t_1 (shift a_1 i_4) in 0%Z ≤ i_4 -> i_4 < x_7 -> (to_uint8 x_9 = to_uint8 x_10) = (x_9 = x_10)) -> i = 1%Z.
Admitted.
