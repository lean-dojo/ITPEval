(*
  Statement-only formalization of Logipedia corpus artifact
  leibniz.refl_leibniz, catalog title "leibniz.refl_leibniz": for every type
  and element, Leibniz equality relates the element to itself. This file
  contains no proof.
*)

let statement =
  `!x:'a.
     !P:'a->bool. P x ==> P x`;;
