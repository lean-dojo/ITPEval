(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1999_b6:
  a finite set of integers greater than one with the stated gcd-selection
  property contains two elements whose gcd is prime. This file contains no
  proof.
*)

let statement =
  `let integer_prime =
     \p:int.
       &1 < p /\
       !d:int. d divides p ==> abs d = &1 \/ abs d = p in
   !S:int->bool.
     FINITE S /\
     (!s:int. s IN S ==> &1 < s) /\
     (!n:int.
        ?s:int.
          s IN S /\ (gcd(s,n) = &1 \/ gcd(s,n) = s))
     ==> ?s t:int.
           s IN S /\ t IN S /\ integer_prime (gcd(s,t))`;;
