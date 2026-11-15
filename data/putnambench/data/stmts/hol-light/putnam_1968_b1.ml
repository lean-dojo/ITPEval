(*
  Statement-only formalization of PutnamBench artifact putnam_1968_b1:
  the probability identity relating the minimum and maximum of two
  finite-range integer-valued random variables. This file contains no proof.
*)

let statement =
  `let seq_tends =
     \(u:num->real) l.
       !e. &0 < e ==> ?N. !n. N <= n ==> abs (u n - l) < e in
   let probability_space =
     \(events:(A->bool)->bool) (p:(A->bool)->real).
       {} IN events /\
       (:A) IN events /\
       (!s:A->bool. s IN events ==> (:A) DIFF s IN events) /\
       (!sets:num->A->bool.
          (!n. sets n IN events)
          ==> {w:A | ?n. w IN sets n} IN events) /\
       p {} = &0 /\
       p (:A) = &1 /\
       (!s:A->bool. s IN events ==> &0 <= p s) /\
       (!sets:num->A->bool.
          (!n. sets n IN events) /\
          (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
          ==> seq_tends
                (\n. sum {j:num | j < n} (\j. p (sets j)))
                (p {w:A | ?j. w IN sets j})) in
   let integer_random_variable =
     \(events:(A->bool)->bool) (X:A->int).
       !s:int->bool. {w:A | X w IN s} IN events in
   !events:(A->bool)->bool
    p:(A->bool)->real
    X:A->int
    Y:A->int
    k:int.
      probability_space events p /\
      integer_random_variable events X /\
      integer_random_variable events Y /\
      FINITE (IMAGE X (:A)) /\
      FINITE (IMAGE Y (:A))
      ==> p {w:A | (if X w <= Y w then X w else Y w) = k} =
          p {w:A | X w = k} +
          p {w:A | Y w = k} -
          p {w:A | (if X w <= Y w then Y w else X w) = k}`;;
