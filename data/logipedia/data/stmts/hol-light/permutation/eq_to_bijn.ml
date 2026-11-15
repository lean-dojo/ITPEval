(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.eq_to_bijn, catalog title "permutation.eq_to_bijn": bounded
  surjectivity on the natural-number initial segment through n is preserved
  when two functions agree throughout that segment. This file contains no
  proof.
*)

let statement =
  `!f g:num->num.
   !n:num.
     (!i:num. i <= n ==> f i = g i)
     ==> (!m:num. m <= n ==> ?p:num. p <= n /\ f p = m)
     ==> (!m:num. m <= n ==> ?p:num. p <= n /\ g p = m)`;;
