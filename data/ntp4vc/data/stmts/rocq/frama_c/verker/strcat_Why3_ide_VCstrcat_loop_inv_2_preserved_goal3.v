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
Require Import verker.A_Strlen.A_Strlen.
Require Import Why3.Cint.Cint.
Open Scope Z_scope.
Theorem goal3 (t_1 : addr -> Z) (a_2 : addr) (a : addr) (a_1 : addr) (t : Z -> Z) : let x : Z := t_1 a_2 in let x_1 : Z := l_strlen t_1 a in let a_3 : addr := shift a x_1 in let x_2 : Z := l_strlen t_1 a_1 in ¬ x = 0%Z -> t_1 a_3 = 0%Z -> region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> x_1 + x_2 ≤ 18446744073709551615%Z -> linked t -> sconst t_1 -> addr_le a a_2 -> is_sint8 x -> p_valid_str t t_1 a -> p_valid_str t t_1 a_1 -> p_valid_str t t_1 a_2 -> is_uint64 x_1 -> addr_le a_2 a_3 -> valid_rw t (shift a 0%Z) (1%Z + x_1 + x_2) -> (∀(i : Z), 0%Z ≤ i -> i < x_1 -> ¬ t_1 (shift a i) = 0%Z) -> (∀(i : Z), 0%Z ≤ i -> i + offset a < offset a_2 -> ¬ t_1 (shift a i) = 0%Z) -> p_valid_str t t_1 (shift a_2 1%Z).
Admitted.
