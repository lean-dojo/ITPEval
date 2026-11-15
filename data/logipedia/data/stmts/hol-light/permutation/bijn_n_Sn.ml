(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.bijn_n_Sn, catalog title "permutation.bijn_n_Sn": bounded
  surjectivity of a natural-number function extends from the initial segment
  through n to the segment through SUC n when the new endpoint is fixed.
  This file contains no proof.
*)

let statement =
  `!f:num->num.
   !n:num.
     (!m:num.
        m <= n
        ==> ?p:num. p <= n /\ f p = m)
     ==> f (SUC n) = SUC n
     ==> (!m:num.
            m <= SUC n
            ==> ?p:num. p <= SUC n /\ f p = m)`;;
