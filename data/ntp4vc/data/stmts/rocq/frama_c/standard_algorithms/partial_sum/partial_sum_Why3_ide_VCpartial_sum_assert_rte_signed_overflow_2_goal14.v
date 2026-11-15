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
Require Import Why3.Cint.Cint.
Require Import partial_sum.Compound.Compound.
Require Import partial_sum.Axiomatic1.Axiomatic1.
Require Import partial_sum.A_AccumulateAxiomatic.A_AccumulateAxiomatic.
Require Import partial_sum.Axiomatic.Axiomatic.
Open Scope Z_scope.
Theorem goal14 (a : addr) (a_1 : addr) (t_2 : addr -> Z) (t_1 : addr -> Z) (i : Z) (i_1 : Z) (t : Z -> Z) : let a_2 : addr := shift a 0%Z in let a_3 : addr := shift a_1 0%Z in let x : Z := t_2 a_3 in let a_4 : addr -> Z := havoc t_1 (fun_updt t_2 a_2 x) (shift a 1%Z) (i - 1%Z) in let x_1 : Z := i_1 - 1%Z in let a_5 : Z := a_4 (shift a x_1) in let a_6 : Z := a_4 (shift a_1 i_1) in let a_7 : Z := a_4 (shift a (to_uint32 x_1)) in a_5 = l_accumulate_1' a_4 a_1 i_1 0%Z -> 0%Z < i -> 0%Z < i_1 -> i_1 ≤ i -> i_1 < i -> region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> linked t -> is_uint32 i -> is_uint32 i_1 -> is_sint32 x -> valid_rd t a_3 1%Z -> valid_rd t a_3 i -> valid_rw t a_2 1%Z -> valid_rw t a_2 i -> p_accumulatebounds_1' t_2 a_1 (1%Z + i) 0%Z -> separated a_3 i a_2 i -> is_sint32 a_6 -> is_sint32 a_5 -> is_sint32 a_7 -> p_unchanged_1' a_4 t_2 a_1 0%Z i -> p_partialsum a_4 a_1 i_1 a -> a_6 + a_7 ≤ 2147483647%Z.
Admitted.
