(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1979_b3:
  the number of constant shifts of an irreducible monic quadratic over a
  finite field of odd order that remain irreducible. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory groupTheory ringTheory;

val putnam_1979_b3 =
  ``!(r : 'a ring) (n : num) (b c : 'a).
      let polynomials =
        {p : num -> 'a |
           (!k : num. p k IN r.carrier) /\
           FINITE {k : num | p k <> r.sum.id}};
          poly_zero = (\k : num. r.sum.id);
          poly_one =
            (\k : num. if k = 0 then r.prod.id else r.sum.id);
          poly_add =
            (\p q : num -> 'a.
               \k : num. r.sum.op (p k) (q k));
          poly_mul =
            (\p q : num -> 'a.
               \k : num.
                 ITSET
                   (\i acc. r.sum.op (r.prod.op (p i) (q (k - i))) acc)
                   (count (SUC k))
                   r.sum.id);
          poly_ring =
            (<| carrier := polynomials;
                sum :=
                  <| carrier := polynomials;
                     op := poly_add;
                     id := poly_zero |>;
                prod :=
                  <| carrier := polynomials;
                     op := poly_mul;
                     id := poly_one |> |>
             : (num -> 'a) ring);
          quadratic =
            (\k : num.
               if k = 0 then c
               else if k = 1 then b
               else if k = 2 then r.prod.id
               else r.sum.id);
          constant =
            (\d : 'a.
               \k : num. if k = 0 then d else r.sum.id)
      in
        Ring r /\
        Group (r.prod excluding r.sum.id) /\
        FINITE r.carrier /\
        CARD r.carrier = n /\
        ODD n /\
        b IN r.carrier /\
        c IN r.carrier /\
        irreducible poly_ring quadratic
        ==>
        CARD
          {d : 'a |
             d IN r.carrier /\
             irreducible
               poly_ring
               (poly_add quadratic (constant d))} =
        (n - 1) DIV 2``;
