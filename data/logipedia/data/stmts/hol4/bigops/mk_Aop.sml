(*
  Statement-only formalization of the Logipedia corpus artifact bigops.mk_Aop:
  left and right identity and associativity of a binary operation imply the
  opaque Aop predicate for its neutral element. This file contains no proof.
*)

open HolKernel Parse boolLib;

val _ = new_constant (
  "logipedia_bigops_Aop",
  Type.alpha --> Type.bool);

val bigops_mk_Aop =
  ``!(nil : 'a) (op : 'a -> 'a -> 'a).
      (!a : 'a. op nil a = a)
      ==>
      (!a : 'a. op a nil = a)
      ==>
      (!a : 'a.
        !b : 'a.
          !c : 'a.
            op a (op b c) = op (op a b) c)
      ==>
      logipedia_bigops_Aop nil``;
