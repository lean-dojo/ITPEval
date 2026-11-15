(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1077462, "König's theorem (set theory)": for indexed families of sets,
  pointwise strict inequality of the fiber cardinalities makes the cardinality
  of their indexed disjoint union strictly smaller than that of the dependent
  function space. This file contains no proof.
*)

open HolKernel Parse boolLib;
open cardinalTheory pred_setTheory;

val konig_sum_lt_product =
  ``!(A : 'i -> 'a set) (B : 'i -> 'b set).
      (!i. A i <</= B i)
      ==>
      {p : 'i # 'a | SND p IN A (FST p)}
        <</=
      {h : 'i -> 'b | !i. h i IN B i}``;
