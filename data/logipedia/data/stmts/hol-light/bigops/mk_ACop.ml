(*
  Statement-only formalization of Logipedia corpus artifact bigops.mk_ACop,
  catalog title "bigops.mk_ACop": a binary operation with a two-sided identity,
  associativity, and commutativity entails the source ACop predicate for that
  identity element. This file contains no proof.
*)

new_constant
  ("logipedia_bigops_ACop", `:'a -> bool`);;

let statement =
  `!nil:A. !op:A->A->A.
     (!a:A. op nil a = a)
     ==>
     (!a:A. op a nil = a)
     ==>
     (!a b c:A. op a (op b c) = op (op a b) c)
     ==>
     (!a b:A. op a b = op b a)
     ==>
     logipedia_bigops_ACop nil`;;
