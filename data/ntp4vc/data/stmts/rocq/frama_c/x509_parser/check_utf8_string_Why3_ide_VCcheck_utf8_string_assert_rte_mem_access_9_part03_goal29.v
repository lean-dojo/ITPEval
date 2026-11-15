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
Require Import Why3.Cbits.Cbits.
Open Scope Z_scope.
Theorem goal29 (a_1 : addr) (t_1 : addr -> Z) (i : Z) (i_1 : Z) (a : addr) (t : Z -> Z) : let a_2 : addr := shift a_1 0%Z in let a_3 : addr := shift a_1 1%Z in let x : Z := t_1 a_3 in let a_4 : addr := shift a_1 2%Z in let x_1 : Z := t_1 a_4 in let a_5 : addr := shift a_1 3%Z in ¬ i = 0%Z -> ¬ i_1 = 0%Z -> ¬ Mk_addr 0%Z 0%Z = a -> t_1 a_2 = 244%Z -> land 192%Z x = 128%Z -> land 192%Z x_1 = 128%Z -> 0%Z ≤ i_1 -> region (base a) ≤ 0%Z -> 4%Z ≤ i -> 128%Z ≤ x -> x ≤ 143%Z -> linked t -> is_uint16 i -> is_uint16 i_1 -> is_uint8 x -> is_uint8 x_1 -> is_uint8 (t_1 a_5) -> valid_rd t a_2 1%Z -> valid_rd t a_2 i -> valid_rd t a_3 1%Z -> valid_rd t a_4 1%Z -> (0%Z < i_1 -> valid_rd t (shift a 0%Z) i_1) -> valid_rd t a_5 1%Z.
Admitted.
