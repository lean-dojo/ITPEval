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
Require Import verker.A_Strlen.A_Strlen.
Require Import verker.Compound.Compound.
Open Scope Z_scope.
Theorem goal4 (a_1 : addr) (a : addr) (t_2 : addr -> Z) (t_1 : addr -> Z) (i_1 : Z) (i : Z) (t : Z -> Z) : let x : Z := base a_1 in let x_1 : Z := base a in let x_2 : Z := l_strlen t_2 a in let a_2 : addr := shift a_1 0%Z in let a_3 : addr -> Z := havoc t_1 t_2 a_2 i_1 in let a_4 : addr -> Z := fun_updt a_3 (shift a_1 i_1) 0%Z in ¬ i = 0%Z -> ¬ x = x_1 -> t_2 (shift a x_2) = 0%Z -> region x_1 ≤ 0%Z -> region x ≤ 0%Z -> linked t -> sconst t_2 -> is_uint64 i -> is_uint64 i_1 -> p_valid_str t t_2 a -> is_uint64 x_2 -> valid_rd t (shift a 0%Z) i_1 -> valid_rw t a_2 i -> valid_rw t a_2 i_1 -> p_valid_str t a_4 a_1 -> (if decide (i ≤ x_2) then to_uint64 (i - 1%Z) = i_1 else x_2 = i_1) -> (∀(i_2 : Z), 0%Z ≤ i_2 -> i_2 < x_2 -> ¬ t_2 (shift a i_2) = 0%Z) -> (∀(i_2 : Z), 0%Z ≤ i_2 -> i_2 < i_1 -> a_3 (shift a_1 i_2) = a_3 (shift a i_2)) -> l_strlen a_4 a_1 = i_1.
Admitted.
