(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1996_a4:
  a ternary orientation relation on a finite set satisfying cyclic, reversal,
  and four-point compatibility conditions admits a compatible injective
  real-valued ordering. This file contains no proof.
*)

let statement =
  `!S:(A#A#A)->bool.
     FINITE (UNIV:A->bool) /\
     (!a b c:A.
        S (a,b,c)
        ==> ~(a = b) /\ ~(b = c) /\ ~(a = c)) /\
     (!a b c:A.
        ~(a = b) /\ ~(b = c) /\ ~(a = c)
        ==> (S (a,b,c) <=> S (b,c,a))) /\
     (!a b c:A.
        ~(a = b) /\ ~(b = c) /\ ~(a = c)
        ==> (S (a,b,c) <=> ~(S (c,b,a)))) /\
     (!a b c d:A.
        ~(a = b) /\ ~(a = c) /\ ~(a = d) /\
        ~(b = c) /\ ~(b = d) /\ ~(c = d)
        ==> ((S (a,b,c) /\ S (c,d,a)) <=>
             (S (b,c,d) /\ S (d,a,b))))
     ==> ?g:A->real.
           (!a b:A. g a = g b ==> a = b) /\
           (!a b c:A.
              g a < g b /\ g b < g c
              ==> S (a,b,c))`;;
