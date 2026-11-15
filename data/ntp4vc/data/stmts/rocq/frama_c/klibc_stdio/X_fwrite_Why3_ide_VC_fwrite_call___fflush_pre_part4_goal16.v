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
Require Import klibc_stdio.Compound.Compound.
Require Import Why3.Cint.Cint.
Require Import klibc_stdio.Axiomatic3.Axiomatic3.
Open Scope Z_scope.
Theorem goal16 (i_3 : Z) (i_4 : Z) (a_4 : addr) (a_5 : addr) (a_2 : addr) (a : addr) (t_1 : addr -> Z) (t_2 : addr -> Z) (i_5 : Z) (t_3 : addr -> addr) (t : Z -> Z) (a_1 : addr) (a_3 : addr) (i : Z) (i_1 : Z) (i_2 : Z) : let x : Z := i_3 + i_4 in let a_6 : addr := shift a_4 0%Z in let a_7 : addr := shift a_5 0%Z in ¬ i_4 = 0%Z -> shift a_2 0%Z = shift a 0%Z -> t_1 (shift a_5 10%Z) = 1%Z -> t_2 (shift a_4 (to_uint32 (i_4 - 1%Z))) = 10%Z -> 0%Z ≤ i_3 -> 0%Z ≤ i_4 -> 0%Z ≤ i_5 -> 0%Z ≤ x -> region (base a_2) ≤ 0%Z -> region (base a_4) ≤ 0%Z -> framed t_3 -> linked t -> sconst t_2 -> is_uint32 i_3 -> is_uint32 i_4 -> is_uint32 i_5 -> is_uint32 x -> p_valid_io_file_pvt t t_3 t_1 a_1 -> p_valid_io_file_pvt t t_3 t_1 a_3 -> p_valid_io_file_pvt t t_3 t_1 a_5 -> valid_rw t a_6 i_4 -> valid_rw t a_6 x -> (∀(i_6 : Z), i_4 < i_6 -> i_6 ≤ x -> ¬ t_2 (shift a_4 (i_6 - 1%Z)) = 10%Z) -> p_valid_io_file_pvt t t_3 (fun_updt (fun_updt (fun_updt t_1 (shift a_5 8%Z) i) (shift a_7 1%Z) i_1) (shift a_7 2%Z) i_2) a_5.
Admitted.
