(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1984_b5:
  the alternating power sum weighted by binary digit counts has the closed
  form 2^(m(m-1)/2) times m!, up to sign. This file contains no proof.
*)

let statement =
  `!d:num->num. !m:num.
     0 < m /\
     (!n:num.
        d n =
        if n < 2 then n
        else n MOD 2 + d (n DIV 2))
     ==> sum (0..2 EXP m - 1)
             (\k. (-- &1) pow (d k) * (&k) pow m) =
         (-- &1) pow m *
         (&2) pow ((m * (m - 1)) DIV 2) *
         &(FACT m)`;;
