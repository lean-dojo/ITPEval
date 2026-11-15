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
Require Import Why3.Cbits.Cbits.
Require Import x509_parser.Compound.Compound.
Open Scope Z_scope.
Theorem goal5 (a_1 : addr) (a : addr) (a_2 : addr) (i_1 : Z) (i : Z) (i_2 : Z) (t : Z -> Z) (t_1 : addr -> Z) : let x : Z := base a_1 in let x_1 : Z := base a in let x_2 : Z := base a_2 in ¬ i_1 = 0%Z -> ¬ a_2 = a -> ¬ Mk_addr 0%Z 0%Z = a_1 -> ¬ x = x_1 -> ¬ x_2 = x -> 0%Z ≤ i -> 0%Z ≤ i_1 -> region x_1 ≤ 0%Z -> region x ≤ 0%Z -> region x_2 ≤ 0%Z -> i_2 < lsl 1%Z (to_uint32 (7%Z * i)) -> i ≤ 3%Z -> i ≤ 4%Z -> 5%Z ≤ i_1 -> lsl i_2 7%Z ≤ 4294967295%Z -> linked t -> is_uint16 i -> is_uint16 i_1 -> is_uint32 i_2 -> valid_rw t a 1%Z -> valid_rw t a_2 1%Z -> (0%Z < i_1 -> valid_rd t (shift a_1 0%Z) i_1) -> (∀(i_3 : Z), 0%Z ≤ i_3 -> i_3 < i -> bit_test (t_1 (shift a_1 i_3)) 7%Z) -> valid_rd t (shift a_1 i) 1%Z.
Admitted.
