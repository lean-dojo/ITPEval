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
Require Import verker.A_Ctype.A_Ctype.
Open Scope Z_scope.
Theorem goal6 (t_1 : addr -> Z) (a : addr) (a_1 : addr) (i : Z) (t : Z -> Z) (a_2 : addr) (t_2 : addr -> Z) : let x : Z := l_strlen t_1 a in let a_3 : addr := shift a (x - 1%Z) in let x_1 : Z := t_1 a_3 in let x_2 : Z := t_1 a_1 in ¬ i = 0%Z -> ¬ x = 0%Z -> t_1 (shift a x) = 0%Z -> ¬ x_1 = 0%Z -> 0%Z < x -> region (base a) ≤ 0%Z -> linked t -> sconst t_1 -> is_uint8 i -> addr_le a a_1 -> is_sint8 x_2 -> p_isspace x_2 -> p_valid_str t t_1 a -> is_uint64 x -> addr_lt (shift a_1 (- 1%Z)) a_2 -> addr_le (shift a (- 1%Z)) a_1 -> addr_le a_1 a_3 -> addr_le a_2 a_3 -> is_sint8 x_1 -> (∀(i_1 : Z), 0%Z ≤ i_1 -> i_1 < x -> ¬ t_1 (shift a i_1) = 0%Z) -> (∀(a_4 : addr), addr_lt a_1 a_4 -> addr_le a_4 a_3 -> p_isspace (t_1 a_4)) -> p_isspace (t_2 a_2).
Admitted.
