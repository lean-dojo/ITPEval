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
Theorem goal16 (t_2 : addr -> Z) (a : addr) (i_2 : Z) (a_1 : addr) (i_1 : Z) (i : Z) (t_1 : addr -> Z) (i_3 : Z) (t : Z -> Z) : let x : Z := t_2 (shift a i_2) in let a_2 : addr := shift a_1 0%Z in let x_1 : Z := i_1 - i in let a_3 : addr -> Z := havoc t_1 t_2 a_2 x_1 in let a_4 : addr := shift a x_1 in let a_5 : addr := shift a 0%Z in let a_6 : addr := shift a_1 x_1 in let a_7 : addr -> Z := fun_updt a_3 a_6 x in ¬ i = 0%Z -> x = to_sint8 i_3 -> a_3 a_4 = x -> 0%Z < i_1 -> 0%Z ≤ i -> i ≤ i_1 -> 0%Z ≤ i_2 -> i_2 < i_1 -> region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> - 128%Z ≤ i_3 -> i_3 ≤ 127%Z -> linked t -> sconst t_2 -> is_uint32 i -> is_uint32 i_1 -> is_sint32 i_3 -> valid_rw t a_5 i_1 -> valid_rw t a_2 i_1 -> separated a_5 i_1 a_2 i_1 -> addr_le a a_4 -> addr_le a_1 a_6 -> addr_le a_4 (shift a i_1) -> addr_le a_6 (shift a_1 i_1) -> (∀(i_4 : Z), 0%Z ≤ i_4 -> i_4 + i < i_1 -> a_3 (shift a_1 i_4) = a_3 (shift a i_4)) -> (∀(i_4 : Z), 0%Z ≤ i_4 -> i_4 + i < i_1 -> ¬ a_3 (shift a_1 i_4) = x) -> a_7 a_4 = x ∧ 0%Z < i ∧ (∀(i_4 : Z), 0%Z ≤ i_4 -> i_4 + i ≤ i_1 -> a_7 (shift a_1 i_4) = a_7 (shift a i_4)) ∧ (∀(i_4 : Z), 0%Z ≤ i_4 -> i_4 + i < i_1 -> ¬ a_7 (shift a i_4) = x).
Admitted.
