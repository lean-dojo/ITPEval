(*
  Statement-only formalization of Logipedia corpus artifact
  leibniz.sym_leibniz, catalog title "leibniz.sym_leibniz": for every type
  and elements x and y, Leibniz equality from x to y entails Leibniz equality
  from y to x. This file contains no proof.
*)

let statement =
  `!x y:'a.
     (!P:'a->bool. P x ==> P y)
     ==>
     (!P:'a->bool. P y ==> P x)`;;
