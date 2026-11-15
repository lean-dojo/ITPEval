(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1566341, "Hindman's theorem": every finite cover of the finite-product set
  of an infinite sequence in a semigroup has a member containing the
  finite-product set of another infinite sequence. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory;

val hindman_fp_partition_regular =
  ``let finite_products =
      \(mul : 'a -> 'a -> 'a) (a : num -> 'a) (x : 'a).
        ?indices : num list.
          indices <> [] /\
          (!i j.
             i < j /\ j < LENGTH indices
             ==>
             EL i indices < EL j indices) /\
          x =
            FOLDL
              mul
              (a (HD indices))
              (MAP a (TL indices))
    in
      !(mul : 'a -> 'a -> 'a)
       (a : num -> 'a)
       (s : ('a set) set).
        (!x y z. mul (mul x y) z = mul x (mul y z)) /\
        FINITE s /\
        finite_products mul a SUBSET BIGUNION s
        ==>
        ?c : 'a set.
          c IN s /\
          ?b : num -> 'a.
            finite_products mul b SUBSET c``;
