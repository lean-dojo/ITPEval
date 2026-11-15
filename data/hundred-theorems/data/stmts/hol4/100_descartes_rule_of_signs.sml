(*
  Statement-only formalization of "Descartes Rule of Signs" from Hundred
  Theorems artifact hundred-theorems__hol4__100. It states that the sign
  variations of a nonzero real polynomial's coefficients equal the total
  multiplicity of its positive real roots plus an even number. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory real_sigmaTheory;

val descartes_rule_of_signs =
  ``let variation =
      \(s : num set) (a : num -> real).
        CARD
          {pq : num # num |
             FST pq IN s /\
             SND pq IN s /\
             FST pq < SND pq /\
             a (FST pq) * a (SND pq) < 0 /\
             !i.
               i IN s /\ FST pq < i /\ i < SND pq
               ==> a i = 0}
    in
      let multiplicity =
        \(f : real -> real) (r : real).
          @k : num.
            ?b : num -> real. ?m : num.
              SIGMA
                (\i. b i * r pow i)
                (count (SUC m)) <> 0 /\
              !x.
                f x =
                (x - r) pow k *
                SIGMA
                  (\i. b i * x pow i)
                  (count (SUC m))
      in
        !(f : real -> real) (a : num -> real) (n : num).
          f =
            (\x.
               SIGMA
                 (\i. a i * x pow i)
                 (count (SUC n))) /\
          (?i. i IN count (SUC n) /\ a i <> 0)
          ==>
          ?d : num.
            EVEN d /\
            variation (count (SUC n)) a =
              SIGMA
                (\r. multiplicity f r)
                {r : real | 0 < r /\ f r = 0} +
              d``;
