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
Require Import verker.A_StrPBrk.A_StrPBrk.
Require Import verker.A_StrSpn.A_StrSpn.
Require Import verker.Compound.Compound.
Require Import verker.A_Strlen.A_Strlen.
Require Import Why3.Cint.Cint.
Open Scope Z_scope.
Theorem goal11 (t_1 : addr -> Z) (a : addr) (a_2 : addr) (a_1 : addr) (t : Z -> Z) (a_3 : addr) : let x : Z := t_1 a in ¬ x = 0%Z -> l_strpbrk a_2 a_1 = l_strpbrk a a_1 -> region (base a_1) ≤ 0%Z -> region (base a_2) ≤ 0%Z -> linked t -> sconst t_1 -> addr_lt a_3 a_1 -> addr_le a_1 a_3 -> addr_le a_2 a -> is_sint8 x -> p_valid_str t t_1 a -> p_valid_str t t_1 a_1 -> p_valid_str t t_1 a_2 -> addr_le a (shift a_2 (l_strlen t_1 a_2)) -> (∀(a_5 : addr) (a_4 : addr), addr_lt a_5 a -> addr_le a_1 a_4 -> addr_le a_2 a_5 -> addr_lt a_4 (shift a_1 (l_strlen t_1 a_1)) -> ¬ t_1 a_5 = t_1 a_4) -> ¬ t_1 a_3 = x.
Admitted.
