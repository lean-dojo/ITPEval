(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2021_b4
  (putnambench__hol-light__putnam_2021_b4): Fibonacci residues of the
  weighted product of positive integers below a Fibonacci number. This file
  contains no proof.
*)

let statement =
  `!f:num->num.
     ((!n:num.
         f (n + 2) = f (n + 1) + f n) /\
      f 0 = 0 /\
      f 1 = 1)
     ==> !m:num.
           2 < m
           ==> ?p:num.
                 nproduct (1..(f m - 1)) (\k:num. k EXP k) MOD f m =
                 f p`;;
