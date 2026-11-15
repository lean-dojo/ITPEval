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
Require Import klibc_string.A_Length.A_Length.
Require Import klibc_string.Axiomatic.Axiomatic.
Require Import klibc_string.Compound.Compound.
Open Scope Z_scope.
Theorem goal4 (t_1 : addr -> Z) (a : addr) (a_1 : addr) (t : Z -> Z) (i : Z) (i_1 : Z) (i_2 : Z) : let x : Z := l_length t_1 a in let x_1 : Z := 1%Z + x in let x_2 : Z := to_uint32 x_1 in let a_2 : addr := shift a_1 0%Z in ¬ Mk_addr 0%Z 0%Z = a_1 -> ¬ x_2 = 0%Z -> region (base a) ≤ 0%Z -> linked t -> sconst t_1 -> is_sint32 x -> p_length_of_str_is t t_1 a i -> p_length_of_str_is t t_1 a i_1 -> p_length_of_str_is t t_1 a i_2 -> is_sint32 x_1 -> (0%Z < x_2 -> valid_rw t a_2 x_2) -> separated (shift a 0%Z) x_2 a_2 x_2.
Admitted.
