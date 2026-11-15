(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.bijn_fg, catalog title "permutation.bijn_fg": surjectivity on
  the natural-number initial segment through n is preserved under function
  composition. This file contains no proof.
*)

let statement =
  `!f g:num->num.
   !n:num.
     (!m:num. m <= n ==> ?p:num. p <= n /\ f p = m)
     ==> (!m:num. m <= n ==> ?p:num. p <= n /\ g p = m)
     ==> (!m:num. m <= n ==> ?p:num. p <= n /\ f (g p) = m)`;;
