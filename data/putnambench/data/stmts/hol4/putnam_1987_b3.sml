(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1987_b3:
  the rational parametrization of the unit circle over an arbitrary field of
  characteristic not two. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory;

val putnam_1987_b3 =
  ``!(zeroR oneR : 'a)
      (addR mulR : 'a -> 'a -> 'a)
      (negR invR : 'a -> 'a).
      let field_axioms =
        (zeroR <> oneR /\
         (!x. addR zeroR x = x) /\
         (!x. addR (negR x) x = zeroR) /\
         (!x y. addR x y = addR y x) /\
         (!x y z. addR (addR x y) z = addR x (addR y z)) /\
         (!x. mulR oneR x = x) /\
         (!x y. mulR x y = mulR y x) /\
         (!x y z. mulR (mulR x y) z = mulR x (mulR y z)) /\
         (!x y z.
            mulR x (addR y z) = addR (mulR x y) (mulR x z)) /\
         (!x. x <> zeroR ==> mulR (invR x) x = oneR))
      in
      let square = \x : 'a. mulR x x;
          sub = \x y : 'a. addR x (negR y);
          divide = \x y : 'a. mulR x (invR y)
      in
        field_axioms /\
        addR oneR oneR <> zeroR
        ==>
        {p : 'a # 'a |
           addR (square (FST p)) (square (SND p)) = oneR} =
        ({(oneR, zeroR)} UNION
         {p : 'a # 'a |
            ?r : 'a.
              square r <> negR oneR /\
              p =
                (divide
                   (sub (square r) oneR)
                   (addR (square r) oneR),
                 divide
                   (mulR (addR oneR oneR) r)
                   (addR (square r) oneR))})``;
