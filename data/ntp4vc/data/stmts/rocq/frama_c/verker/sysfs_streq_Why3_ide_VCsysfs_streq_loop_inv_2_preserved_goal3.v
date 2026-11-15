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
Require Import verker.A_Strlen.A_Strlen.
Require Import verker.Compound.Compound.
Require Import Why3.Cint.Cint.
Require Import verker.A_StrnCmp.A_StrnCmp.
Require Import verker.A_Strnlen.A_Strnlen.
Open Scope Z_scope.
Theorem goal3 (a_1 : addr) (i : Z) (t_1 : addr -> Z) (a : addr) (t : Z -> Z) : let a_2 : addr := shift a_1 i in let x : Z := t_1 a_2 in let a_3 : addr := shift a i in let x_1 : Z := t_1 a_3 in let x_2 : Z := 1%Z + i in ¬ x = 0%Z -> x = x_1 -> i ≤ l_strlen t_1 a -> i ≤ l_strlen t_1 a_1 -> region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> linked t -> sconst t_1 -> is_uint64 i -> p_valid_str t t_1 a -> p_valid_str t t_1 a_1 -> p_strnequal t_1 a_1 a i -> is_sint8 x_1 -> is_sint8 x -> p_valid_str t t_1 a_3 -> p_valid_str t t_1 a_2 -> (∀(i_1 : Z), 0%Z ≤ i_1 -> i_1 < i -> t_1 (shift a_1 i_1) = t_1 (shift a i_1)) -> x_2 = to_uint64 x_2.
Admitted.
