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
Require Import klibc_string.Compound.Compound.
Open Scope Z_scope.
Theorem goal5 (i_1 : Z) (a : addr) (a_1 : addr) (i : Z) (t : Z -> Z) (t_1 : addr -> Z) : let x : Z := to_uint32 (1%Z + i_1) in let a_2 : addr := shift a 0%Z in ¬ Mk_addr 0%Z 0%Z = a_1 -> ¬ x = 0%Z -> 0%Z ≤ i -> region (base a) ≤ 0%Z -> linked t -> sconst t_1 -> is_uint32 i -> is_uint32 i_1 -> valid_rw t a_2 i -> (0%Z < x -> valid_rw t (shift a_1 0%Z) x) -> ((∀(i_2 : Z), 0%Z ≤ i_2 -> i_2 < i -> ¬ t_1 (shift a i_2) = 0%Z) -> i_1 = i) -> ((∃(i_2 : Z), t_1 (shift a i_2) = 0%Z ∧ 0%Z ≤ i_2 ∧ i_2 < i) -> i_1 ≤ i) -> valid_rw t a_2 i_1.
Admitted.
