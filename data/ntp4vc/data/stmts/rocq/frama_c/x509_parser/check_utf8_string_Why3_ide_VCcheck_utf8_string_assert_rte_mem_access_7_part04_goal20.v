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
Theorem goal20 (a_1 : addr) (t_1 : addr -> Z) (i : Z) (i_1 : Z) (a : addr) (t : Z -> Z) : let a_2 : addr := shift a_1 0%Z in let x : Z := t_1 a_2 in ¬ i = 0%Z -> ¬ i_1 = 0%Z -> ¬ Mk_addr 0%Z 0%Z = a -> ¬ x = 240%Z -> ¬ x = 244%Z -> 0%Z ≤ i_1 -> region (base a) ≤ 0%Z -> 4%Z ≤ i -> 128%Z ≤ x -> 194%Z ≤ x -> 224%Z ≤ x -> 240%Z ≤ x -> x ≤ 244%Z -> linked t -> is_uint16 i -> is_uint16 i_1 -> is_uint8 x -> valid_rd t a_2 1%Z -> valid_rd t a_2 i -> (0%Z < i_1 -> valid_rd t (shift a 0%Z) i_1) -> valid_rd t (shift a_1 1%Z) 1%Z.
Admitted.
