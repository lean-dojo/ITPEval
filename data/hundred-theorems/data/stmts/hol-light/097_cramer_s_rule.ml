(*
  Statement-only formalization of "Cramer's Rule" from Hundred Theorems
  artifact 097 (hundred-theorems__hol-light__097). It states the determinant
  formula for the unique solution of a nonsingular real square linear system.
  This file contains no proof.
*)

needs "Multivariate/determinants.ml";;

let HUNDRED_THEOREMS_097_CRAMER =
  `!A:real^N^N x b.
      ~(det A = &0)
      ==> (A ** x = b <=>
           x = lambda k.
                 det((lambda i j.
                        if j = k then b$i else A$i$j):real^N^N) /
                 det A)`;;
