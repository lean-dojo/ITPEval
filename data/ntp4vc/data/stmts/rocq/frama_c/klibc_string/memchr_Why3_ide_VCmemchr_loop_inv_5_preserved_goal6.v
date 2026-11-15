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
Require Import klibc_string.Compound.Compound.
Require Import Why3.Cint.Cint.
Open Scope Z_scope.
Theorem goal6 (a : addr) (i_1 : Z) (i : Z) (t_1 : addr -> Z) (i_3 : Z) (i_2 : Z) (t : Z -> Z) : let a_1 : addr := shift a (i_1 - i) in let x : Z := t_1 a_1 in let x_1 : Z := to_sint8 i_3 in ¬ i = 0%Z -> ¬ x = x_1 -> 0%Z < i_1 -> 0%Z ≤ i -> i ≤ i_1 -> 0%Z ≤ i_2 -> region (base a) ≤ 0%Z -> i_2 + to_uint32 (i - 1%Z) < i_1 -> - 128%Z ≤ i_3 -> i_3 ≤ 127%Z -> linked t -> sconst t_1 -> is_uint32 i -> is_uint32 i_1 -> is_sint32 i_3 -> valid_rw t (shift a 0%Z) i_1 -> addr_le a a_1 -> addr_le a_1 (shift a i_1) -> is_sint8 x -> (∀(i_4 : Z), 0%Z ≤ i_4 -> i_4 + i < i_1 -> ¬ t_1 (shift a i_4) = x_1) -> ¬ t_1 (shift a i_2) = x_1.
Admitted.
