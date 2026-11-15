(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.transpose_i_j_j_i, catalog title
  "permutation.transpose_i_j_j_i": transposing two natural-number indices is
  unchanged when the two indices are exchanged. This file contains no proof.
*)

let logipedia_permutation_transpose = new_definition
  `logipedia_permutation_transpose (i:num) (j:num) (n:num) =
     if n = i then j else if n = j then i else n`;;

let statement =
  `!i j n:num.
     logipedia_permutation_transpose i j n =
     logipedia_permutation_transpose j i n`;;
