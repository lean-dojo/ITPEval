(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.falsity, catalog title "connectives.falsity": the distinguished
  False proposition entails every proposition. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_false", `:bool`);;

let statement =
  `!t:bool.
     (logipedia_connectives_false:bool) ==> t`;;
