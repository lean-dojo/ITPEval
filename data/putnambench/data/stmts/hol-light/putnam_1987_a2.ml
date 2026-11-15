(*
  Statement-only formalization of PutnamBench artifact putnam_1987_a2:
  the decimal digit block containing position 10^1987 in the sequence formed
  by concatenating the positive integers has length 1984. This file contains
  no proof.
*)

let statement =
  `let putnam_1987_a2_solution = 1984 in
   !seqind seqsize f numdigits:num->num.
     seqind 1 = 1 /\
     (!i:num.
        2 <= i
        ==> seqind i = seqind (i - 1) + numdigits (i - 1)) /\
     (!i:num.
        1 <= i
        ==> !j:num.
              j < numdigits i
              ==> seqsize (seqind i + j) = numdigits i) /\
     (!n:num. f n = seqsize (10 EXP n)) /\
     (!n:num.
        1 <= n
        ==> 10 EXP (numdigits n - 1) <= n /\
            n < 10 EXP (numdigits n))
     ==> f 1987 = putnam_1987_a2_solution`;;
