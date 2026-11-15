(*
  Statement-only formalization of Logipedia corpus artifact
  relations.RC_reflexive, catalog title "relations.RC_reflexive": adjoining
  equality to an arbitrary binary relation yields a reflexive relation.
  This file contains no proof.
*)

let statement =
  `!(R:A->A->bool) x:A.
     R x x \/ x = x`;;
