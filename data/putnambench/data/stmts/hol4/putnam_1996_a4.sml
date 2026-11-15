(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1996_a4:
  a ternary orientation relation on a finite set satisfying cyclic, reversal,
  and four-point compatibility conditions admits a compatible injective
  real-valued ordering. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory;

val putnam_1996_a4 =
  ``!S : ('a # 'a # 'a) -> bool.
      FINITE (UNIV : 'a set) /\
      (!a b c : 'a.
         S (a, b, c)
         ==>
         a <> b /\ b <> c /\ a <> c) /\
      (!a b c : 'a.
         a <> b /\ b <> c /\ a <> c
         ==>
         (S (a, b, c) <=> S (b, c, a))) /\
      (!a b c : 'a.
         a <> b /\ b <> c /\ a <> c
         ==>
         (S (a, b, c) <=> ~S (c, b, a))) /\
      (!a b c d : 'a.
         a <> b /\ a <> c /\ a <> d /\
         b <> c /\ b <> d /\ c <> d
         ==>
         ((S (a, b, c) /\ S (c, d, a)) <=>
          (S (b, c, d) /\ S (d, a, b))))
      ==>
      ?g : 'a -> real.
        (!a b : 'a. g a = g b ==> a = b) /\
        (!a b c : 'a.
           g a < g b /\ g b < g c
           ==>
           S (a, b, c))``;
