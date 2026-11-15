(*
  Statement-only formalization of the Babel-formal artifact lattice_like:
  partial-order, meet, and join laws on the whole ambient type, together with
  commutativity, associativity, and absorption identities. This file contains
  no proof.
*)

open HolKernel Parse boolLib;

val lattice_like_def = new_definition (
  "lattice_like_def",
  ``lattice_like (le_rel : 'a -> 'a -> bool)
                  (inf_op : 'a -> 'a -> 'a)
                  (sup_op : 'a -> 'a -> 'a) <=>
      (!x. le_rel x x) /\
      (!x y z. le_rel x y ==> le_rel y z ==> le_rel x z) /\
      (!x y. le_rel x y ==> le_rel y x ==> x = y) /\
      (!a b. le_rel (inf_op a b) a) /\
      (!a b. le_rel (inf_op a b) b) /\
      (!c a b. le_rel c a ==> le_rel c b ==> le_rel c (inf_op a b)) /\
      (!a b. le_rel a (sup_op a b)) /\
      (!a b. le_rel b (sup_op a b)) /\
      (!a b c. le_rel a c ==> le_rel b c ==> le_rel (sup_op a b) c)``);

val inf_comm =
  ``!(le_rel : 'a -> 'a -> bool)
      (inf_op : 'a -> 'a -> 'a)
      (sup_op : 'a -> 'a -> 'a).
      lattice_like le_rel inf_op sup_op ==>
      !a b. inf_op a b = inf_op b a``;

val sup_comm =
  ``!(le_rel : 'a -> 'a -> bool)
      (inf_op : 'a -> 'a -> 'a)
      (sup_op : 'a -> 'a -> 'a).
      lattice_like le_rel inf_op sup_op ==>
      !a b. sup_op a b = sup_op b a``;

val inf_assoc =
  ``!(le_rel : 'a -> 'a -> bool)
      (inf_op : 'a -> 'a -> 'a)
      (sup_op : 'a -> 'a -> 'a).
      lattice_like le_rel inf_op sup_op ==>
      !a b c. inf_op (inf_op a b) c = inf_op a (inf_op b c)``;

val sup_assoc =
  ``!(le_rel : 'a -> 'a -> bool)
      (inf_op : 'a -> 'a -> 'a)
      (sup_op : 'a -> 'a -> 'a).
      lattice_like le_rel inf_op sup_op ==>
      !a b c. sup_op (sup_op a b) c = sup_op a (sup_op b c)``;

val inf_absorption =
  ``!(le_rel : 'a -> 'a -> bool)
      (inf_op : 'a -> 'a -> 'a)
      (sup_op : 'a -> 'a -> 'a).
      lattice_like le_rel inf_op sup_op ==>
      !a b. inf_op a (sup_op a b) = a``;

val sup_absorption =
  ``!(le_rel : 'a -> 'a -> bool)
      (inf_op : 'a -> 'a -> 'a)
      (sup_op : 'a -> 'a -> 'a).
      lattice_like le_rel inf_op sup_op ==>
      !a b. sup_op a (inf_op a b) = a``;
