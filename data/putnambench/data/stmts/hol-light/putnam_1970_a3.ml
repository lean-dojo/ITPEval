(*
  Statement-only formalization of PutnamBench artifact putnam_1970_a3:
  the longest nonzero repeated terminal decimal digit run among perfect
  squares has length 3, first attained by the square 1444. This file contains
  no proof.
*)

let statement =
  `!digits:num->num list. !runlen:num->num.
     (!n:num.
        digits n =
        if n < 10 then [n]
        else CONS (n MOD 10) (digits (n DIV 10))) /\
     (!n:num.
        runlen n <= LENGTH (digits n) /\
        (!k:num.
           k < runlen n
           ==> EL k (digits n) = EL 0 (digits n)) /\
        (~(runlen n = LENGTH (digits n))
         ==> ~(EL (runlen n) (digits n) = EL 0 (digits n))))
     ==>
     (?n:num.
        ~(EL 0 (digits (n EXP 2)) = 0) /\
        runlen (n EXP 2) = 3) /\
     (!n:num.
        ~(EL 0 (digits (n EXP 2)) = 0)
        ==> runlen (n EXP 2) <= 3) /\
     (?m:num. m EXP 2 = 1444) /\
     runlen 1444 = 3 /\
     ~(EL 0 (digits 1444) = 0) /\
     (!n:num.
        ~(EL 0 (digits (n EXP 2)) = 0) /\
        runlen (n EXP 2) = 3
        ==> 1444 <= n EXP 2)`;;
