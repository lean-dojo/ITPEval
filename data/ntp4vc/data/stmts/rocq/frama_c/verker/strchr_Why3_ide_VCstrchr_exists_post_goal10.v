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
Require Import verker.A_Strchr.A_Strchr.
Require Import verker.Compound.Compound.
Require Import Why3.Cint.Cint.
Require Import verker.A_Strlen.A_Strlen.
Open Scope Z_scope.
Theorem goal10 (t_1 : addr -> Z) (a_3 : addr) (a : addr) (a_1 : addr) (a_2 : addr) (i : Z) (t : Z -> Z) : let x : Z := t_1 a_3 in let x_1 : Z := t_1 a in let x_2 : Z := t_1 a_1 in let a_4 : addr := shift a_2 (l_strlen t_1 a_2) in x = to_sint8 i -> l_strchr t_1 a_2 x = l_strchr t_1 a_1 x -> region (base a_2) ≤ 0%Z -> linked t -> sconst t_1 -> is_sint32 i -> addr_le a_2 a_1 -> addr_le a_2 a_3 -> is_sint8 x_1 -> is_sint8 x_2 -> p_valid_str t t_1 a_1 -> p_valid_str t t_1 a_2 -> addr_le a_1 a_4 -> addr_le a_3 a_4 -> (if decide (x = x_2) then a_1 = a ∧ (a_4 = a) = (x_1 = 0%Z) ∧ addr_lt a a_4 = (¬ x_1 = 0%Z) else Mk_addr 0%Z 0%Z = a ∧ x_2 = 0%Z) -> (∀(a_5 : addr), addr_lt a_5 a_1 -> addr_le a_2 a_5 -> ¬ x = t_1 a_5) -> addr_le a_2 a ∧ addr_le a a_4.
Admitted.
