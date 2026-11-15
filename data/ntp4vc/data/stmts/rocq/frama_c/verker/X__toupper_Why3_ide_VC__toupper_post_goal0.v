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
Require Import verker.A_Ctype.A_Ctype.
Require Import Why3.Cint.Cint.
Open Scope Z_scope.
Theorem goal0 (i_1 : Z) (i : Z) (i_2 : Z) (fact0 : p_islower (to_sint8 i_1) = (¬ i = 0%Z)) (fact1 : is_uint8 i) (fact2 : is_uint8 i_1) (fact3 : is_uint8 i_2) (fact4 : if decide (i = 0%Z) then i_2 = i_1 else to_uint8 (i_1 - 32%Z) = i_2) : l_toupper i_1 = i_2.
Admitted.
