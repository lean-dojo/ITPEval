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
Theorem goal31 (t_2 : addr -> addr) (a_1 : addr) (a : addr) (t_1 : addr -> Z) (i : Z) (i_1 : Z) (t : Z -> Z) : let a_2 : addr := t_2 (shift a_1 5%Z) in let x : Z := base a_2 in let x_1 : Z := base a in let x_2 : Z := base (t_2 (shift a_1 6%Z)) in let x_3 : Z := t_1 (shift a_1 9%Z) in let x_4 : Z := t_1 (shift (shift a_1 0%Z) 0%Z) in ¬ i = 0%Z -> t_1 (shift a_1 7%Z) = 0%Z -> x = x_1 -> x_2 = x_1 -> x_2 = x -> 0%Z ≤ i -> i_1 ≤ i -> region (base a_1) ≤ 0%Z -> - 1%Z ≤ i_1 -> framed t_2 -> linked t -> is_uint32 i -> is_sint32 i_1 -> is_uint32 x_3 -> is_uint32 (t_1 (shift a_1 8%Z)) -> p_valid_io_file_pvt t t_2 t_1 a_1 -> addr_le a_2 a -> valid_rw t (shift a 0%Z) i -> is_sint32 x_4 -> addr_le a (shift a_2 (32%Z + x_3)) -> 0%Z ≤ x_4.
Admitted.
