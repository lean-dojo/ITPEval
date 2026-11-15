(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1077462,
  "König's theorem (set theory)": pointwise strict domination of cardinal
  families makes their indexed cardinal sum strictly smaller than their
  indexed cardinal product. This file contains no proof.
*)

let KONIGS_THEOREM_SET_THEORY =
  `!k:I->bool f:I->A->bool g:I->B->bool.
      (!i:I. i IN k ==> f i <_c g i)
      ==> {p:I#A | FST p IN k /\ SND p IN f (FST p)} <_c
          cartesian_product k g`;;
