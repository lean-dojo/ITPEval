(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1052678 (thousand-theorems__hol4__Q1052678), "Baire category theorem": in a
  Baire topological space, the intersection of any countable family of open
  dense sets is dense. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory topologyTheory;

val q1052678_baire_space_def = new_definition (
  "q1052678_baire_space_def",
  ``q1052678_baire_space (top : 'a topology) <=>
      !(f : num -> 'a set).
        (!n : num. open_in top (f n)) /\
        (!n : num. top closure_of (f n) = topspace top)
        ==>
        top closure_of (BIGINTER (IMAGE f UNIV)) = topspace top``);

val dense_sInter_of_isOpen =
  ``!(top : 'a topology) (S : ('a set) set).
      topspace top = UNIV /\
      q1052678_baire_space top /\
      (!s : 'a set. s IN S ==> open_in top s) /\
      COUNTABLE S /\
      (!s : 'a set. s IN S ==> top closure_of s = topspace top)
      ==>
      top closure_of (BIGINTER S) = topspace top``;
