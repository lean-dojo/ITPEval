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
Open Scope Z_scope.
Theorem goal4 (t_2 : addr -> Z) (a_1 : addr) (t_1 : addr -> Z) (a : addr) (t : Z -> Z) (i : Z) (i_1 : Z) (t_3 : addr -> Z) : let x : Z := l_strlen t_2 a_1 in let a_2 : addr := shift a_1 x in let a_3 : addr -> Z := havoc t_1 t_2 (shift a_1 0%Z) x in let a_4 : Z := a_3 a in t_2 a_2 = 0%Z -> ¬ a_4 = 0%Z -> region (base a_1) ≤ 0%Z -> linked t -> sconst t_2 -> is_sint8 i -> is_sint8 i_1 -> addr_le a_1 a -> p_valid_str t t_2 a_1 -> is_uint64 x -> addr_le a a_2 -> is_sint8 a_4 -> p_valid_str t a_3 a -> p_valid_str t a_3 a_1 -> (if decide (a_4 = i) then fun_updt a_3 a i_1 = t_3 else a_3 = t_3) -> (∀(i_2 : Z), 0%Z ≤ i_2 -> i_2 < x -> ¬ t_2 (shift a_1 i_2) = 0%Z) -> (∀(a_5 : addr), addr_le a a_5 -> addr_lt a_5 a_2 -> a_3 a_5 = t_2 a_5) -> (∀(a_5 : addr), t_2 a_5 = i -> addr_lt a_5 a -> addr_le a_1 a_5 -> a_3 a_5 = i_1) -> (∀(a_5 : addr), let x_1 : Z := t_2 a_5 in ¬ x_1 = i -> addr_lt a_5 a -> addr_le a_1 a_5 -> a_3 a_5 = x_1) -> p_valid_str t t_3 (shift a 1%Z).
Admitted.
