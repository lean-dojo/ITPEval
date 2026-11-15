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
Theorem goal6 (t_1 : addr -> addr) (a : addr) (i_1 : Z) (i_2 : Z) (a_1 : addr) (i : Z) (t : Z -> Z) : let a_2 : addr := t_1 a in let x : Z := i_1 + i_2 in let a_3 : addr := t_1 (shift a_1 x) in let a_4 : addr := t_1 (shift a_3 0%Z) in let x_1 : Z := 1%Z + i_2 in ¬ a_2 = Mk_addr 0%Z 0%Z -> ¬ a_4 = Mk_addr 0%Z 0%Z -> 0%Z ≤ i_2 -> i_2 < i -> region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> framed t_1 -> linked t -> is_sint32 i -> is_sint32 i_1 -> is_sint32 i_2 -> valid_rw t a 1%Z -> is_sint32 x_1 -> valid_rw t (shift a_1 0%Z) 2147483646%Z -> p_linked_n t t_1 a_2 a_1 i_1 i (Mk_addr 0%Z 0%Z) -> p_linked_n t t_1 a_2 a_1 i_1 i_2 a_3 -> p_linked_n t t_1 a_3 a_1 x (i - i_2) (Mk_addr 0%Z 0%Z) -> p_linked_n t t_1 a_2 a_1 i_1 x_1 a_4.
Admitted.
