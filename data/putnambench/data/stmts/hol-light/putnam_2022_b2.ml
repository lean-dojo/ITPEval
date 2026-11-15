(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2022_b2:
  classification of the positive cardinalities of finite subsets of real
  three-space that are exactly closed under pairwise cross products. This file
  contains no proof.
*)

let statement =
  `let cross3 =
     \(v:real^3) (w:real^3).
       (lambda i.
          if i = 1 then v$2 * w$3 - v$3 * w$2
          else if i = 2 then v$3 * w$1 - v$1 * w$3
          else v$1 * w$2 - v$2 * w$1):real^3 in
   !n:num.
     (0 < n /\
      ?S:real^3->bool.
        FINITE S /\
        CARD S = n /\
        S =
          {u:real^3 |
             ?v w:real^3.
               v IN S /\ w IN S /\ u = cross3 v w})
     <=> n = 1 \/ n = 7`;;
