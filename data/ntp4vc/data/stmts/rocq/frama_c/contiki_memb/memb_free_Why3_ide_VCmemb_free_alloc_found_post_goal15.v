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
Theorem goal15 (a_1 : addr) (t_2 : addr -> Z) (t_5 : addr -> addr) (i_1 : Z) (i : Z) (a : addr) (t : Z -> Z) (t_4 : addr -> Z) (t_1 : Z -> Z) (t_3 : addr -> Z) : let a_2 : addr := shift a_1 1%Z in let x : Z := t_2 a_2 in let a_3 : addr := shift a_1 3%Z in let a_4 : addr := shift a_1 2%Z in let a_5 : addr := shift (t_5 a_4) i_1 in l__memb_index t_5 t_2 a_1 (l__memb_ptr t_5 t_2 a_1 i) = i -> 0%Z ≤ i -> i ≤ x -> region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> framed t_5 -> linked t -> sconst t_4 -> is_sint32 i -> is_sint32 i_1 -> is_uint16 x -> p_valid_memb t t_5 t_2 a_1 -> p__memb_has t_5 t_2 a_1 a -> valid_rd t a_3 1%Z -> valid_rd t a_2 1%Z -> p__memb_allocated t_5 t_4 t_2 a_1 a -> (if decide (i < x) then i_1 = i ∧ t_1 = t ∧ l__memb_ptr t_5 t_2 a_1 i_1 = a ∧ fun_updt t_4 a_5 0%Z = t_3 ∧ valid_rd t_1 a_4 1%Z ∧ valid_rd t_1 a_5 1%Z ∧ valid_rw t_1 a_5 1%Z else t_4 = t_3) -> (∀(i_2 : Z), 0%Z ≤ i_2 -> i_2 < i -> ¬ shift (t_5 a_3) (i_2 * t_2 (shift a_1 0%Z)) = a) -> ¬ p__memb_allocated t_5 t_3 t_2 a_1 a.
Admitted.
