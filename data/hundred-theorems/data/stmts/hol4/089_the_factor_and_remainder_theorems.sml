(*
  Statement-only formalization of "The Factor and Remainder Theorems" from
  Hundred Theorems artifact 089. For a polynomial over a commutative ring,
  division by X - a has constant remainder p(a), and X - a divides p exactly
  when p(a) is zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory ringTheory;

val factor_and_remainder_theorems =
  ``!(r : 'a ring) (p : num -> 'a) (a : 'a) (N : num).
      Ring r /\
      a IN r.carrier /\
      (!n. p n IN r.carrier) /\
      (!n. N <= n ==> p n = r.sum.id)
      ==>
      let value =
        FOLDR
          (\c acc. r.sum.op c (r.prod.op acc a))
          r.sum.id
          (GENLIST p N)
      in
        (?M q.
           (!n. q n IN r.carrier) /\
           (!n. M <= n ==> q n = r.sum.id) /\
           (!n.
              p n =
                if n = 0 then
                  r.sum.op
                    (r.prod.op (r.sum.inv a) (q 0))
                    value
                else
                  r.sum.op
                    (r.prod.op (r.sum.inv a) (q n))
                    (q (PRE n)))) /\
        (value = r.sum.id <=>
         ?M q.
           (!n. q n IN r.carrier) /\
           (!n. M <= n ==> q n = r.sum.id) /\
           (!n.
              p n =
                if n = 0 then
                  r.prod.op (r.sum.inv a) (q 0)
                else
                  r.sum.op
                    (r.prod.op (r.sum.inv a) (q n))
                    (q (PRE n))))``;
