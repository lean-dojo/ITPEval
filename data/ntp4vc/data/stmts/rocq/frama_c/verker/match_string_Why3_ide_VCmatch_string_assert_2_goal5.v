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
Require Import verker.Compound.Compound.
Require Import verker.A_StrCmp.A_StrCmp.
Require Import Why3.Cint.Cint.
Require Import verker.A_Strlen.A_Strlen.
Require Import verker.A_MatchString.A_MatchString.
Open Scope Z_scope.
Theorem goal5 (t_2 : addr -> addr) (a_1 : addr) (i_1 : Z) (t_1 : addr -> Z) (a : addr) (i_2 : Z) (i : Z) (i_3 : Z) (t : Z -> Z) : let a_2 : addr := t_2 (shift a_1 i_1) in let x : Z := l_strcmp t_1 a_2 a in let x_1 : Z := t_1 (shift a_2 i_2) in let x_2 : Z := t_1 (shift a i_2) in let x_3 : Z := l_real_len t_2 a_1 i in let x_4 : Z := l_strlen t_1 a_2 in let a_3 : addr := shift a_1 0%Z in ¬ a_2 = Mk_addr 0%Z 0%Z -> ¬ x = 0%Z -> ¬ x_1 = x_2 -> ¬ t_1 (shift a_2 i_3) = t_1 (shift a i_3) -> 0%Z ≤ i_1 -> 0%Z ≤ i_2 -> 0%Z ≤ i_3 -> to_uint64 i_1 < i -> region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> x_3 ≤ i -> i_1 ≤ x_3 -> i_2 ≤ x_4 -> i_3 ≤ x_4 -> i ≤ 2147483647%Z -> framed t_2 -> linked t -> sconst t_1 -> is_sint32 i_1 -> is_uint64 i -> p_valid_str t t_1 a -> p_valid_str t t_1 a_2 -> is_sint32 x -> (if decide (to_uint8 x_1 < to_uint8 x_2) then x = - 1%Z else x = 1%Z) -> (x_3 = i -> valid_rw t a_3 i) -> (x_3 < i -> valid_rw t a_3 (1%Z + x_3)) -> x = - 1%Z ∨ x = 1%Z -> (∀(i_4 : Z), 0%Z ≤ i_4 -> i_4 < i_1 -> p_valid_str t t_1 (t_2 (shift a_1 i_4))) -> (∀(i_4 : Z), 0%Z ≤ i_4 -> i_4 < i_2 -> t_1 (shift a_2 i_4) = t_1 (shift a i_4)) -> (∀(i_4 : Z), 0%Z ≤ i_4 -> i_4 < i_1 -> ¬ l_strcmp t_1 (t_2 (shift a_1 i_4)) a = 0%Z) -> (∀(i_4 : Z), 0%Z ≤ i_4 -> i_4 < x_3 -> is_uint64 i_4 -> p_valid_str t t_1 (t_2 (shift a_1 i_4))) -> (∃(i_4 : Z), ¬ t_1 (shift a_2 i_4) = t_1 (shift a i_4) ∧ 0%Z ≤ i_4 ∧ i_4 ≤ Z.min (l_strlen t_1 a) x_4 ∧ is_uint64 i_4).
Admitted.
