(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1188392,
  "Zeckendorf's theorem": every natural number has a unique representation as
  a sum of Fibonacci numbers with distinct, nonconsecutive indices at least
  two. This file contains no proof.
*)

let q1188392_fib_pair = new_recursive_definition num_RECURSION
  `(q1188392_fib_pair 0 = (0,1)) /\
   (!n. q1188392_fib_pair (SUC n) =
        (SND (q1188392_fib_pair n),
         FST (q1188392_fib_pair n) + SND (q1188392_fib_pair n)))`;;

let q1188392_fib = new_definition
  `q1188392_fib n = FST (q1188392_fib_pair n)`;;

let Q1188392_ZECKENDORF_THEOREM =
  `let is_zeckendorf_rep =
     \l:num list.
       (!i. i < LENGTH l ==> 2 <= EL i l) /\
       (!i. i + 1 < LENGTH l ==> EL (i + 1) l + 2 <= EL i l) in
   let fib_sum =
     \l:num list. ITLIST (\k total. q1188392_fib k + total) l 0 in
   !n:num. ?!l:num list. is_zeckendorf_rep l /\ fib_sum l = n`;;
