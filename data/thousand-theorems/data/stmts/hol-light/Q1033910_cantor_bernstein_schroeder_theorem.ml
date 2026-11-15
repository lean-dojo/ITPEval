(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1033910,
  "Cantor–Bernstein–Schroeder theorem": injections in both directions between
  two arbitrary, possibly empty sets imply a bijection between them. This file
  contains no proof.
*)

let Q1033910_CANTOR_BERNSTEIN_SCHROEDER_THEOREM =
  `!s:A->bool t:B->bool f:A->B g:B->A.
      INJ f s t /\ INJ g t s
      ==> ?h:A->B. BIJ h s t`;;
