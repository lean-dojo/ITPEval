(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.match_Or_prop, catalog title "connectives.match_Or_prop": for
  propositions A, B, and return_, rules deriving return_ from either A or B,
  together with the distinguished disjunction proposition connectives.Or A B,
  entail return_. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_or", `:bool -> bool -> bool`);;

let statement =
  `!A B return_:bool.
     (A ==> return_)
     ==> (B ==> return_)
     ==> (logipedia_connectives_or:bool->bool->bool) A B
     ==> return_`;;
