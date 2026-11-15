(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2016_a5:
  every element of the stated finite two-generated group is a bounded product
  of signed g-h factors when g has odd order. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory groupTheory;

val putnam_2016_a5 =
  ``!(grp : 'a group) (g h : 'a).
      let S =
        {grp.op g h;
         grp.op (grp.inv g) h;
         grp.op g (grp.inv h);
         grp.op (grp.inv g) (grp.inv h)}
      in
        FiniteGroup grp /\
        (Generated_subset grp {g; h}).carrier = grp.carrier /\
        (Generated_subset grp {g}).carrier <> grp.carrier /\
        (Generated_subset grp {h}).carrier <> grp.carrier /\
        ODD (order grp g)
        ==>
        !x : 'a.
          x IN grp.carrier
          ==>
          ?mn : 'a list.
            1 <= LENGTH mn /\
            LENGTH mn <= CARD grp.carrier /\
            !i : num.
              i < LENGTH mn
              ==>
              EL i mn IN S /\
              x = FOLDR grp.op grp.id mn``;
