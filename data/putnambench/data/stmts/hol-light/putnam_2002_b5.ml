(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2002_b5:
  existence of a natural number that is a three-digit palindrome in at least
  2002 natural-number bases. This file contains no proof.
*)

let statement =
  `!digits:num->num->num list.
     (!b n:num.
        digits b n =
        if b < 2 then REPLICATE n 1
        else if n < b then [n]
        else CONS (n MOD b) (digits b (n DIV b)))
     ==> ?n:num.
           2002 <=
           CARD
             {b:num |
                1 <= b /\
                LENGTH (digits b n) = 3 /\
                digits b n = REVERSE (digits b n)}`;;
