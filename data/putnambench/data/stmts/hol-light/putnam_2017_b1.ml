(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2017_b1
  (putnambench__hol-light__putnam_2017_b1): an intersection criterion for two
  distinct affine lines in the real plane using scaled displacement vectors.
  This file contains no proof.
*)

let statement =
  `let lines =
     {L:real^2->bool |
        ?v:real^2 w:real^2.
          ~(w$1 = &0 /\ w$2 = &0) /\
          L = {p:real^2 |
                 ?t:real.
                   p$1 = v$1 + t * w$1 /\
                   p$2 = v$2 + t * w$2}} in
   !L1:real^2->bool L2:real^2->bool.
     L1 IN lines /\
     L2 IN lines /\
     ~(L1 = L2)
     ==>
     (~(L1 INTER L2 = {}) <=>
      !lam:real.
        ~(lam = &0)
        ==> !P:real^2.
              ~(P IN L1) /\ ~(P IN L2)
              ==> ?A1:real^2 A2:real^2.
                    A1 IN L1 /\
                    A2 IN L2 /\
                    A2$1 - P$1 = lam * (A1$1 - P$1) /\
                    A2$2 - P$2 = lam * (A1$2 - P$2))`;;
