(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1984_a6:
  dependence of the last nonzero digit of a factorial at sums of distinct
  powers of 5 on the exponent sum, and least eventual period 4. This file
  contains no proof.
*)

let statement =
  `!f:num->num.
     (!n:num.
        ?j:num.
          (!i:num.
             i < j
             ==> (FACT n DIV (10 EXP i)) MOD 10 = 0) /\
          ~((FACT n DIV (10 EXP j)) MOD 10 = 0) /\
          f n = (FACT n DIV (10 EXP j)) MOD 10)
     ==>
     ?g:num->num.
       (!k:num. !a:num->num.
          0 < k /\
          (!i j:num.
             i < k /\ j < k /\ a i = a j
             ==> i = j)
          ==>
          f (nsum (0..k - 1) (\i. 5 EXP (a i))) =
          g (nsum (0..k - 1) (\i. a i))) /\
       (!s:num. 1 <= s ==> g (s + 4) = g s) /\
       (!q:num.
          0 < q /\
          (!s:num. 1 <= s ==> g (s + q) = g s)
          ==> 4 <= q)`;;
