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
Theorem goal2 (a_1 : addr) (t_1 : addr -> Z) (a : addr) (i : Z) (t : Z -> Z) : let x : Z := offset a_1 in let x_1 : Z := l_strlen t_1 a_1 in let x_2 : Z := offset a in let x_3 : Z := to_uint64 (x_2 - x) in t_1 a = 0%Z -> x + x_1 = x_2 + l_strlen t_1 a -> 0%Z ≤ i -> region (base a_1) ≤ 0%Z -> i < x_3 -> linked t -> sconst t_1 -> addr_le a_1 a -> p_valid_str t t_1 a -> p_valid_str t t_1 a_1 -> addr_le a (shift a_1 x_1) -> is_sint8 (t_1 (shift a_1 x_3)) -> ¬ t_1 (shift a_1 i) = 0%Z.
Admitted.
