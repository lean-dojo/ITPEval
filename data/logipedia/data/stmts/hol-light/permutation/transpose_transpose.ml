(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.transpose_transpose, catalog title
  "permutation.transpose_transpose": applying the same transposition of two
  natural numbers twice returns the original number. This file contains no
  proof.
*)

let logipedia_permutation_transpose = new_definition
  `logipedia_permutation_transpose (i:num) (j:num) (n:num) =
     if n = i then j else if n = j then i else n`;;

let statement =
  `!i j n:num.
     logipedia_permutation_transpose i j
       (logipedia_permutation_transpose i j n) = n`;;
