(*
  Statement-only formalization of Thousand Theorems corpus artifact Q716171
  (thousand-theorems__hol-light__Q716171), "Erdős–Ginzburg–Ziv theorem":
  among any finite family of at least
  2 * n - 1 integer representatives, some n indexed terms have sum divisible
  by n, equivalently sum zero in Z/nZ. This file contains no proof.
*)

let Q716171_ERDOS_GINZBURG_ZIV_THEOREM =
  `!n:num. !s:A->bool. !a:A->int.
     FINITE s /\ 2 * n - 1 <= CARD s
     ==> ?t:A->bool.
           t SUBSET s /\
           CARD t = n /\
           (&n:int) divides isum t a`;;
