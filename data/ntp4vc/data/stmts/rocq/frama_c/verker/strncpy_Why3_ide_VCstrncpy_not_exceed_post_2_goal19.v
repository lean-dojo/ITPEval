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
Require Import verker.A_Strnlen.A_Strnlen.
Open Scope Z_scope.
Theorem goal19 (a_3 : addr) (a_1 : addr) (a : addr) (t_1 : addr -> Z) (t_2 : addr -> Z) (t_3 : addr -> Z) (t : Z -> Z) (a_2 : addr) : let x : Z := base a_3 in let x_1 : Z := base a_1 in let a_4 : addr := shift a_1 0%Z in let x_2 : Z := offset a_1 in let x_3 : Z := offset a in let x_4 : Z := x_3 - x_2 in ¬ x = x_1 -> havoc t_1 t_2 a_4 (1%Z + l_strnlen t_3 a_3 0%Z) = t_3 -> x_2 ≤ x_3 -> region x_1 ≤ 0%Z -> region x ≤ 0%Z -> x_3 < x_2 + l_strlen t_2 a_3 -> linked t -> sconst t_2 -> addr_le a_1 a -> addr_le a_3 a_2 -> p_valid_str t t_2 a_3 -> p_valid_str t t_3 a_2 -> is_uint64 x_4 -> p_valid_strn t t_2 a_3 x_4 -> p_valid_strn t t_3 a x_4 -> addr_le a (shift a_1 x_4) -> addr_le a_2 (shift a_3 (l_strnlen t_3 a_3 x_4)) -> valid_rw t a_4 (1%Z + l_strnlen t_2 a_3 x_4) -> (∀(i : Z), 0%Z ≤ i -> i + offset a_3 < offset a_2 -> t_3 (shift a_3 i) = t_3 (shift a_1 i)) -> p_valid_strn t t_3 a_1 x_4.
Admitted.
