(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2014_a5:
  the polynomials P_n(x) = 1 + 2x + ... + n x^(n-1) are relatively prime
  for distinct positive indices. This file contains no proof.
*)

let statement =
  `let eval =
     \p:real list. \x:real.
       ITLIST (\c acc. c + x * acc) p (&0) in
   !P:num->real list.
     (!n:num. P n = list_of_seq (\i. &(i + 1)) n)
     ==>
     !j k:num.
       0 < j /\ 0 < k /\ ~(j = k)
       ==>
       ?a b:real list.
         !x:real.
           eval a x * eval (P j) x +
           eval b x * eval (P k) x = &1`;;
