(*
  Statement-only formalization of the Logipedia corpus artifact
  bigops.mk_ACop: left and right identity, associativity, and commutativity of
  a binary operation imply the opaque ACop predicate for its neutral element.
  This file contains no proof.
*)

open HolKernel Parse boolLib;

val _ = new_constant (
  "logipedia_bigops_ACop",
  Type.alpha --> Type.bool);

val bigops_mk_ACop =
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
      (!a : 'a.
        !b : 'a.
          op a b = op b a)
      ==>
      logipedia_bigops_ACop nil``;
