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
Require Import verker.A_StrCmp.A_StrCmp.
Require Import verker.Compound.Compound.
Require Import Why3.Cint.Cint.
Require Import verker.A_Strlen.A_Strlen.
Open Scope Z_scope.
Theorem goal2 (t_1 : addr -> Z) (a : addr) (a_2 : addr) (a_3 : addr) (a_1 : addr) (t : Z -> Z) : let x : Z := t_1 a in let x_1 : Z := to_uint8 x in let x_2 : Z := t_1 a_2 in let x_3 : Z := offset a_2 in let x_4 : Z := offset a_3 in let x_5 : Z := l_strlen t_1 a_3 in let x_6 : Z := x_3 - x_4 in let x_7 : Z := t_1 (shift a_3 x_6) in let x_8 : Z := t_1 (shift a_1 x_6) in ¬ x_1 = 0%Z -> to_uint8 x_2 = x_1 -> l_strcmp t_1 a_3 a_1 = l_strcmp t_1 a_2 a -> offset a_1 + x_3 = offset a + x_4 -> x_4 + x_5 = x_3 + l_strlen t_1 a_2 -> x_7 = x_8 -> (∀(i : Z), 0%Z ≤ i -> i ≤ x_5 -> to_uint8 (t_1 (shift a_3 i)) = to_uint8 (t_1 (shift a_1 i))) = (∀(i : Z), 0%Z ≤ i -> i ≤ x_5 -> t_1 (shift a_3 i) = t_1 (shift a_1 i)) -> region (base a_1) ≤ 0%Z -> region (base a_3) ≤ 0%Z -> linked t -> sconst t_1 -> addr_le a_1 a -> addr_le a_3 a_2 -> is_sint8 x -> is_sint8 x_2 -> p_valid_str t t_1 a -> p_valid_str t t_1 a_1 -> p_valid_str t t_1 a_2 -> p_valid_str t t_1 a_3 -> addr_le a (shift a_1 (l_strlen t_1 a_1)) -> addr_le a_2 (shift a_3 x_5) -> is_sint8 x_8 -> is_sint8 x_7 -> (∀(i : Z), 0%Z ≤ i -> i + x_4 < x_3 -> t_1 (shift a_3 i) = t_1 (shift a_1 i)) -> p_valid_str t t_1 (shift a 1%Z) ∧ p_valid_str t t_1 (shift a_2 1%Z).
Admitted.
