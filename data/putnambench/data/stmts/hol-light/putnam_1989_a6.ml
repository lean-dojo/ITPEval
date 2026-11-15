(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1989_a6:
  a binary-coefficient formal power series defined by even zero-block lengths
  in binary expansions satisfies a cubic identity. This file contains no proof.
*)

let statement =
  `let binary_digits =
     \(n:num) (ds:num list).
       (!i:num. i < LENGTH ds ==> EL i ds < 2) /\
       ITLIST (\d acc. d + 2 * acc) ds 0 = n /\
       (n = 0 <=> ds = []) /\
       (0 < n ==> LAST ds = 1) in
   let digits =
     \n:num. @ds:num list. binary_digits n ds in
   let good =
     \n:num.
       let bin = CONS 1 (APPEND (digits n) [1]) in
       !i j:num.
         i < LENGTH bin /\
         j < LENGTH bin /\
         i < j /\
         EL i bin = 1 /\
         EL j bin = 1 /\
         (!k:num. i < k /\ k < j ==> EL k bin = 0)
         ==> EVEN (j - i - 1) in
   let ps_add =
     \(a:num->bool) (b:num->bool) (n:num). ~(a n <=> b n) in
   let ps_mul =
     \(a:num->bool) (b:num->bool) (n:num).
       ODD (CARD {k:num | k <= n /\ a k /\ b (n - k)}) in
   let ps_one = \n:num. n = 0 in
   let ps_X = \n:num. n = 1 in
   let alpha = \n:num. good n in
   !n:num.
     ps_add
       (ps_add
         (ps_mul (ps_mul alpha alpha) alpha)
         (ps_mul ps_X alpha))
       ps_one n =
     F`;;
