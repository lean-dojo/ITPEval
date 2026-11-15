(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3527102,
  "Kruskal-Katona theorem": among finite families of r-element subsets of
  Fin n, an initial colex segment has no larger shadow than any family with
  at least as many members. This file contains no proof.
*)

let Q3527102_KRUSKAL_KATONA_THEOREM =
  `let fin_n_set =
     \(n:num) (s:num->bool).
       FINITE s /\ s SUBSET {i:num | i < n} in
   let uniform_family =
     \(n:num) (r:num) (family:(num->bool)->bool).
       FINITE family /\
       (!s:num->bool. s IN family ==> fin_n_set n s /\ CARD s = r) in
   let colex_le =
     \(s:num->bool) (t:num->bool).
       s = t \/
       (?m:num.
          m IN t /\ ~(m IN s) /\
          (!j:num. m < j ==> (j IN s <=> j IN t))) in
   let initial_colex_segment =
     \(n:num) (r:num) (family:(num->bool)->bool).
       uniform_family n r family /\
       (!s t:num->bool.
          s IN family /\
          fin_n_set n t /\
          CARD t = r /\
          colex_le t s
          ==> t IN family) in
   let shadow =
     \(family:(num->bool)->bool).
       {t:num->bool |
          ?a:num. ~(a IN t) /\ (a INSERT t) IN family} in
   !n r:num.
   !family initial:(num->bool)->bool.
     uniform_family n r family /\
     CARD initial <= CARD family /\
     initial_colex_segment n r initial
     ==> CARD (shadow initial) <= CARD (shadow family)`;;
