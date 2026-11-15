(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2002_a3:
  parity of the number of nonempty subsets of {1,...,n} whose average is an
  integer. This file contains no proof.
*)

let statement =
  `!n Tn:int.
     &2 <= n /\
     Tn =
       &(CARD
           {S:int->bool |
              S SUBSET {x:int | &1 <= x /\ x <= n} /\
              ~(S = {}) /\
              (?k:int.
                 real_of_int k =
                 (&1 / &(CARD S)) *
                 sum S (\s:int. real_of_int s))})
     ==> ?m:int. Tn - n = &2 * m`;;
