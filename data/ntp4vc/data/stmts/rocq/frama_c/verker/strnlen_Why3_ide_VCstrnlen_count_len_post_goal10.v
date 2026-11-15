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
Require Import verker.A_Strnlen.A_Strnlen.
Require Import verker.Compound.Compound.
Require Import Why3.Cint.Cint.
Require Import verker.A_Strlen.A_Strlen.
Open Scope Z_scope.
Theorem goal10 (a_1 : addr) (a : addr) (i : Z) (t_1 : addr -> Z) (t : Z -> Z) : let x : Z := offset a_1 in let x_1 : Z := offset a in let x_3 : Z := i + x_1 - x in let x_4 : Z := l_strnlen t_1 a_1 x_3 in let x_5 : Z := i + x_1 in ¬ i = 0%Z -> t_1 a = 0%Z -> x + x_4 = x_1 + l_strnlen t_1 a i -> 0%Z ≤ i -> x ≤ x_1 -> region (base a_1) ≤ 0%Z -> linked t -> sconst t_1 -> is_uint64 i -> addr_le a_1 a -> p_valid_strn t t_1 a i -> is_uint64 x_3 -> p_valid_strn t t_1 a_1 x_3 -> addr_le a (shift a_1 x_4) -> (∀(i_1 : Z), 0%Z ≤ i_1 -> i_1 + x < x_1 -> ¬ t_1 (shift a_1 i_1) = 0%Z) -> (∀(i_1 : Z), 0%Z ≤ i_1 -> i_1 + x ≤ x_5 -> ¬ t_1 (shift a_1 i_1) = 0%Z) -> x + to_uint64 (x_1 - x) = x_5.
Admitted.
