(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.f_invert_permut, catalog title
  "permutation.f_invert_permut": on a natural-number initial segment, applying
  a permutation to its recursively constructed inverse returns the original
  value. This file contains no proof.
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
   !n m:num.
     m <= n
     ==> logipedia_permutation_permut f n
     ==> f (logipedia_permutation_invert_permut n f m) = m`;;
