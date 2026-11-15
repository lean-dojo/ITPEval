(*
  Statement-only formalization of PutnamBench artifact putnam_1965_b5:
  existence of a finite simple graph with V vertices and E edges and no
  triangles when 4 * E <= V^2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val putnam_1965_b5 =
  ``!V E : num. !vertices : 'a set.
      FINITE vertices /\
      CARD vertices = V /\
      4 * E <= V EXP 2
      ==>
      ?G : ('a # 'a) set.
        FINITE G /\
        (!v w : 'a.
           (v,w) IN G
           ==>
           v IN vertices /\ w IN vertices) /\
        (!v : 'a. (v,v) NOTIN G) /\
        (!v w : 'a. (v,w) IN G <=> (w,v) IN G) /\
        CARD G = 2 * E /\
        ~(?a b c : 'a.
            (b,c) IN G /\
            (c,a) IN G /\
            (a,b) IN G)``;
