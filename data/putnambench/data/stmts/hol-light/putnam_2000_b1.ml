(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2000_b1:
  integer triples with a pointwise odd entry admit an integer linear
  combination that is odd on at least four sevenths of the indices. This file
  contains no proof.
*)

let statement =
  `let odd_integer =
     \x:int. ?k:int. x = &2 * k + &1 in
   !N:num. !a b c:num->int.
     1 <= N /\
     (!j:num.
        j < N
        ==> odd_integer (a j) \/
            odd_integer (b j) \/
            odd_integer (c j))
     ==> ?r s t:int.
           &(CARD
               {j:num |
                  j < N /\
                  odd_integer (r * a j + s * b j + t * c j)}) >=
           (&4 * &N) / &7`;;
