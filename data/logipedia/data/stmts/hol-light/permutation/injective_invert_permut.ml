(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.injective_invert_permut, catalog title
  "permutation.injective_invert_permut": the inverse of a natural-number
  permutation on the initial segment through n is injective on that segment.
  This file contains no proof.
*)

let logipedia_permutation_injn = new_definition
  `logipedia_permutation_injn (f:num->num) (n:num) <=>
     !i j:num.
       i <= n
       ==> j <= n
       ==> f i = f j
       ==> i = j`;;

let logipedia_permutation_permut = new_definition
  `logipedia_permutation_permut (f:num->num) (n:num) <=>
     (!i:num. i <= n ==> f i <= n) /\
     logipedia_permutation_injn f n`;;

let logipedia_permutation_invert_permut =
  new_recursive_definition num_RECURSION
    `(logipedia_permutation_invert_permut
        0 (f:num->num) (m:num) = 0) /\
     (logipedia_permutation_invert_permut
        (SUC n) f m =
          if m = f (SUC n) then SUC n
          else logipedia_permutation_invert_permut n f m)`;;

let statement =
  `!f:num->num.
   !n:num.
     logipedia_permutation_permut f n
     ==>
     logipedia_permutation_injn
       (logipedia_permutation_invert_permut n f)
       n`;;
