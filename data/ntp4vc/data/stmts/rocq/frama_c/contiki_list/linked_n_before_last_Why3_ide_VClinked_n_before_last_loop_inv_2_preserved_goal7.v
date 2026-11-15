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
Require Import contiki_list.Compound.Compound.
Require Import contiki_list.S1_list.S1_list.
Require Import contiki_list.Axiomatic.Axiomatic.
Open Scope Z_scope.
Theorem goal7 (i_1 : Z) (i : Z) (i_2 : Z) (t_1 : addr -> addr) (a_2 : addr) (a : addr) (a_1 : addr) (t : Z -> Z) : let x : Z := 1%Z + i_1 in let x_1 : Z := i + i_2 in let a_3 : addr := t_1 (shift a_2 (i + i_1)) in let x_3 : Z := i + i_2 - 1%Z in 0%Z < i_2 -> 0%Z ≤ i -> 0%Z ≤ i_1 -> i_2 ≤ i_1 -> 0%Z ≤ i_2 -> region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> region (base a_2) ≤ 0%Z -> framed t_1 -> linked t -> is_sint32 i -> is_sint32 i_1 -> is_sint32 i_2 -> is_sint32 (i_2 - 1%Z) -> is_sint32 x -> valid_rw t (shift a_2 0%Z) 2147483646%Z -> p_linked_n t t_1 a a_2 i x a_1 -> p_linked_n t t_1 (t_1 (shift a_2 x_1)) a_2 x_1 (i_1 - i_2) a_3 -> p_linked_n t t_1 (t_1 (shift a_2 x_3)) a_2 x_3 (1%Z + i_1 - i_2) a_3.
Admitted.
