(* Statement-only formalization of PutnamBench corpus artifact putnam_2012_a1:
   among twelve real numbers in the open interval (1, 12), three distinct
   entries form the side lengths of an acute triangle. This file contains no proof. *)

From Stdlib Require Import Reals Vectors.Fin.

Open Scope R_scope.

Theorem putnam_2012_a1
    (d : Fin.t 12 -> Rdefinitions.R)
    (hd : forall i : Fin.t 12, 1 < d i < 12) :
  exists i j k : Fin.t 12,
    i <> j /\
    i <> k /\
    j <> k /\
    d k >= d i /\
    d k >= d j /\
    d i ^ 2 + d j ^ 2 > d k ^ 2.
Admitted.
