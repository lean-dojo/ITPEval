(*
  Statement-only formalization of Logipedia corpus artifact bigops.mk_Aop,
  catalog title "bigops.mk_Aop": a binary operation with a two-sided identity
  and associativity entails the source Aop predicate for that identity element.
  This file contains no proof.
*)

new_constant
  ("logipedia_bigops_Aop", `:'a -> bool`);;

let statement =
  `!nil:A. !op:A->A->A.
     (!a:A. op nil a = a)
     ==>
     (!a:A. op a nil = a)
     ==>
     (!a b c:A. op a (op b c) = op (op a b) c)
     ==>
     logipedia_bigops_Aop nil`;;
