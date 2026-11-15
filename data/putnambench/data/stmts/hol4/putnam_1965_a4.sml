(*
  Statement-only formalization of PutnamBench artifact putnam_1965_a4:
  a finite nonempty bipartite dance relation contains a crossed pair of
  dances and non-dances under the stated incidence assumptions. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory;

val putnam_1965_a4 =
  ``!dances : 'g -> 'b -> bool.
      FINITE (UNIV : 'g set) /\
      FINITE (UNIV : 'b set) /\
      (?g : 'g. T) /\
      (?b : 'b. T) /\
      (~(?b : 'b. !g : 'g. dances g b) /\
       (!g : 'g. ?b : 'b. dances g b))
      ==>
      ?g h : 'g. ?b c : 'b.
        dances g b /\
        dances h c /\
        ~dances h b /\
        ~dances g c``;
