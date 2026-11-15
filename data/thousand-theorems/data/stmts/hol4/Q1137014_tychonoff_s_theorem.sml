(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1137014, "Tychonoff's theorem": a possibly empty indexed product of compact
  subsets is compact in the product topology. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory topologyTheory;

val q1137014_product_carrier_def = new_definition (
  "q1137014_product_carrier_def",
  ``q1137014_product_carrier
      (indices : 'i set) (default : 'a) (top : 'i -> 'a topology) =
      {x : 'i -> 'a |
        (!i. i IN indices ==> x i IN topspace (top i)) /\
        (!i. i NOTIN indices ==> x i = default)}``);

val q1137014_product_basic_open_def = new_definition (
  "q1137014_product_basic_open_def",
  ``q1137014_product_basic_open
      (indices : 'i set) (default : 'a) (top : 'i -> 'a topology)
      (coordinates : 'i set) (u : 'i -> 'a set) =
      {x : 'i -> 'a |
        x IN q1137014_product_carrier indices default top /\
        (!i. i IN coordinates ==> x i IN u i)}``);

val q1137014_product_open_def = new_definition (
  "q1137014_product_open_def",
  ``q1137014_product_open
      (indices : 'i set) (default : 'a) (top : 'i -> 'a topology)
      (U : ('i -> 'a) set) <=>
      U SUBSET q1137014_product_carrier indices default top /\
      !x. x IN U ==>
        ?coordinates u.
          FINITE coordinates /\
          coordinates SUBSET indices /\
          (!i. i IN coordinates ==> open_in (top i) (u i)) /\
          x IN q1137014_product_basic_open
            indices default top coordinates u /\
          q1137014_product_basic_open
            indices default top coordinates u SUBSET U``);

val q1137014_product_compact_def = new_definition (
  "q1137014_product_compact_def",
  ``q1137014_product_compact
      (indices : 'i set) (default : 'a) (top : 'i -> 'a topology)
      (k : ('i -> 'a) set) <=>
      k SUBSET q1137014_product_carrier indices default top /\
      !cover.
        (!v. v IN cover ==>
          q1137014_product_open indices default top v) /\
        k SUBSET UNIONS cover
        ==>
        ?subcover.
          FINITE subcover /\
          subcover SUBSET cover /\
          k SUBSET UNIONS subcover``);

val isCompact_pi_infinite =
  ``!(indices : 'i set) (default : 'a)
      (top : 'i -> 'a topology) (s : 'i -> 'a set).
      (!i. i IN indices ==> compact_in (top i) (s i))
      ==>
      q1137014_product_compact indices default top
        {x : 'i -> 'a |
          (!i. i IN indices ==> x i IN s i) /\
          (!i. i NOTIN indices ==> x i = default)}``;
