(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2007_a5:
  for a finite group, the number of elements of prime order p is either zero
  or one less than a multiple of p. This file contains no proof.
*)

needs "Library/iter.ml";;

let statement =
  `!mul:A->A->A. !e:A. !ginv:A->A. !p n:num.
     FINITE (UNIV:A->bool) /\
     (!a b c:A. mul a (mul b c) = mul (mul a b) c) /\
     (!a:A. mul e a = a /\ mul a e = a) /\
     (!a:A. mul (ginv a) a = e /\ mul a (ginv a) = e) /\
     prime p /\
     n = CARD {g:A |
                 ITER p (mul g) e = e /\
                 (!k:num.
                    0 < k /\ k < p ==> ~(ITER k (mul g) e = e))}
     ==> n = 0 \/ p divides (n + 1)`;;
