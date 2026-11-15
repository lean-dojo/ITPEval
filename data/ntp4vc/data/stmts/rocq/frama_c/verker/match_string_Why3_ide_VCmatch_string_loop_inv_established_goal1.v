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
Theorem goal1 (t_2 : addr -> addr) (a_1 : addr) (i : Z) (a : addr) (t : Z -> Z) (t_1 : addr -> Z) : let x : Z := l_real_len t_2 a_1 i in let a_2 : addr := shift a_1 0%Z in region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> i ≤ 2147483647%Z -> framed t_2 -> linked t -> sconst t_1 -> is_uint64 i -> p_valid_str t t_1 a -> (x = i -> valid_rw t a_2 i) -> (x < i -> valid_rw t a_2 (1%Z + x)) -> (∀(i_1 : Z), 0%Z ≤ i_1 -> i_1 < x -> is_uint64 i_1 -> p_valid_str t t_1 (t_2 (shift a_1 i_1))) -> x ≤ i ∧ 0%Z ≤ x.
Admitted.
