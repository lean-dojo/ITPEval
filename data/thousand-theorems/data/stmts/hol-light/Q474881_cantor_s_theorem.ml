(*
  Statement-only formalization of Thousand Theorems corpus artifact Q474881,
  "Cantor's theorem": no function from a type to its power set is surjective.
  This file contains no proof.
*)

let Q474881_CANTORS_THEOREM =
  `!f:A->(A->bool). ~(!s:A->bool. ?x:A. f x = s)`;;
