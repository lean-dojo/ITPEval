(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2023_b1
  (putnambench__hol-light__putnam_2023_b1): the number of configurations
  reachable by legal diagonal coin slides on an m-by-n grid. This file
  contains no proof.
*)

let binomial_output = open_out "/dev/null";;
let binomial_formatter = Format.formatter_of_out_channel binomial_output;;
let binomial_loaded =
  Toploop.use_file binomial_formatter "Library/binomial.ml";;
Format.pp_print_flush binomial_formatter ();;
close_out binomial_output;;
if not binomial_loaded then failwith "failed to load Library/binomial.ml";;

let statement =
  `let initial =
     \(m:num) (n:num) (i:num) (j:num).
       i <= m - 2 /\ j <= n - 2 in
   let legal_move =
     \(m:num) (n:num)
      (coins1:num->num->bool) (coins2:num->num->bool).
       ?i j:num.
         i < m - 1 /\ j < n - 1 /\
         coins1 i j /\
         ~(coins1 (i + 1) j) /\
         ~(coins1 i (j + 1)) /\
         ~(coins1 (i + 1) (j + 1)) /\
         ~(coins2 i j) /\
         ~(coins2 (i + 1) j) /\
         ~(coins2 i (j + 1)) /\
         coins2 (i + 1) (j + 1) /\
         (!i' j':num.
            ~((i',j') = (i,j)) /\
            ~((i',j') = (i + 1,j)) /\
            ~((i',j') = (i,j + 1)) /\
            ~((i',j') = (i + 1,j + 1))
            ==> coins1 i' j' = coins2 i' j') in
   let legal_sequence =
     \(m:num) (n:num) (seq:(num->num->bool)list).
       ~(seq = []) /\
       HD seq = initial m n /\
       (!k:num.
          k + 1 < LENGTH seq
          ==> legal_move m n (EL k seq) (EL (k + 1) seq)) in
   !m n:num.
     1 < m /\ 1 < n
     ==>
     CARD
       {config:num->num->bool |
          ?seq:(num->num->bool)list.
            legal_sequence m n seq /\ config = LAST seq} =
     binom (m + n - 2,m - 1)`;;
