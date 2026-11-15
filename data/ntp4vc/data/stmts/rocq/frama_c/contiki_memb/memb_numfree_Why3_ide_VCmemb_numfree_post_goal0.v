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
Require Import contiki_memb.Axiomatic13.Axiomatic13.
Require Import Why3.Memory.Memory.
Require Import contiki_memb.Compound.Compound.
Require Import contiki_memb.A_OccArray.A_OccArray.
Require Import Why3.Cint.Cint.
Open Scope Z_scope.
Theorem goal0 (a : addr) (t_1 : addr -> Z) (t_3 : addr -> addr) (t_2 : addr -> Z) (i : Z) (t : Z -> Z) : let a_1 : addr := shift a 1%Z in let x : Z := t_1 a_1 in let a_2 : addr := t_3 (shift a 2%Z) in let x_1 : Z := l_occ_a t_2 0%Z a_2 0%Z i in 0%Z ≤ i -> x ≤ i -> i ≤ x -> region (base a) ≤ 0%Z -> x_1 ≤ i -> framed t_3 -> linked t -> sconst t_2 -> is_sint32 i -> is_uint16 x -> p_valid_memb t t_3 t_1 a -> valid_rd t a_1 1%Z -> is_sint32 x_1 -> l_occ_a t_2 0%Z a_2 0%Z x = l__memb_numfree t_3 t_2 t_1 a.
Admitted.
