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
Require Import x509_parser.Compound.Compound.
Require Import Why3.Cint.Cint.
Open Scope Z_scope.
Theorem goal1 (a_1 : addr) (a : addr) (i_4 : Z) (i_5 : Z) (i : Z) (i_1 : Z) (i_2 : Z) (i_3 : Z) (a_2 : addr) (i_6 : Z) (t : Z -> Z) : let x : Z := base a_1 in let x_1 : Z := base a in let a_3 : addr := shift a_1 i_4 in let a_4 : addr := shift a_1 (i_4 + i_5 - i) in let x_3 : Z := i_4 + i_5 in let x_4 : Z := i_1 - i_2 in ¬ i = 0%Z -> ¬ i_1 = 0%Z -> ¬ i_3 = 0%Z -> ¬ i_5 = 0%Z -> ¬ Mk_addr 0%Z 0%Z = a_1 -> ¬ Mk_addr 0%Z 0%Z = a_2 -> ¬ x = x_1 -> ¬ a_3 = Mk_addr 0%Z 0%Z -> ¬ a_4 = Mk_addr 0%Z 0%Z -> 0%Z ≤ i -> i_6 ≤ i -> 0%Z ≤ i_1 -> i_2 ≤ i_1 -> 0%Z ≤ i_3 -> i_4 ≤ i_3 -> i_5 ≤ i_3 -> 0%Z ≤ i_5 -> 0%Z ≤ i_6 -> x_3 ≤ i_3 -> 0%Z ≤ x_3 -> region x_1 ≤ 0%Z -> region x ≤ 0%Z -> - 2147483648%Z ≤ i -> - 2147483648%Z ≤ i_6 -> 2%Z ≤ i_4 -> 3%Z ≤ i_2 -> i ≤ 65535%Z -> i_6 ≤ 65535%Z -> i ≤ 2147483647%Z -> i_6 ≤ 2147483647%Z -> - 2147483648%Z ≤ x_3 -> x_3 ≤ 65535%Z -> x_3 ≤ 2147483647%Z -> 2%Z + i_6 ≤ i -> i_1 ≤ 65535%Z + i_2 -> i_1 ≤ 2147483647%Z + i_2 -> i_2 ≤ 2147483648%Z + i_1 -> linked t -> is_uint16 i -> is_uint16 i_1 -> is_uint16 i_2 -> is_uint16 i_3 -> is_uint16 i_4 -> is_uint16 i_5 -> is_uint16 i_6 -> valid_rw t a 1%Z -> is_uint16 (i - i_6) -> is_uint16 x_4 -> is_uint16 (i_5 - i) -> valid_rd t (shift a_2 0%Z) i_1 -> (0%Z < i_3 -> valid_rd t (shift a_1 0%Z) i_3) -> (0%Z < i_5 -> valid_rd t a_3 i_5) -> (0%Z < i -> valid_rd t a_4 i) -> valid_rd t (shift a_2 i_2) x_4.
Admitted.
