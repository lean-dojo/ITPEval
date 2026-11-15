(*
  Statement-only formalization of PutnamBench artifact putnam_1976_b3:
  a lower bound for the probability of the intersection of a finite sequence
  of locally dependent events, expressed by a positive recurrence. This file
  contains no proof.
*)

let statement =
  `let seq_tends =
     \(v:num->real) l.
       !e. &0 < e ==> ?N. !m. N <= m ==> abs (v m - l) < e in
   let sigma_algebra =
     \(measurable:(A->bool)->bool).
       {} IN measurable /\
       (:A) IN measurable /\
       (!s:A->bool.
          s IN measurable ==> (:A) DIFF s IN measurable) /\
       (!sets:num->A->bool.
          (!k. sets k IN measurable)
          ==> {w:A | ?k. w IN sets k} IN measurable) in
   let probability_space =
     \(measurable:(A->bool)->bool) (p:(A->bool)->real).
       sigma_algebra measurable /\
       p {} = &0 /\
       p (:A) = &1 /\
       (!s:A->bool. s IN measurable ==> &0 <= p s) /\
       (!sets:num->A->bool.
          (!k. sets k IN measurable) /\
          (!j k. ~(j = k) ==> DISJOINT (sets j) (sets k))
          ==> seq_tends
                (\m. sum {k:num | k < m} (\k. p (sets k)))
                (p {w:A | ?k. w IN sets k})) in
   let independent_events =
     \(p:(A->bool)->real) (s:A->bool) (t:A->bool).
       p (s INTER t) = p s * p t in
   !measurable:(A->bool)->bool
    p:(A->bool)->real
    n:num
    a:real
    u:num->real
    events:num->A->bool.
      probability_space measurable p /\
      1 <= n /\
      &0 <= a /\ a < &1 / &4 /\
      u 0 = &1 /\ u 1 = &1 - a /\
      (!k. 1 <= k
           ==> u (k + 1) = u k - a * u (k - 1)) /\
      (!k. &0 < u k) /\
      (!i. i < n ==> events i IN measurable) /\
      (!i. i < n ==> &1 - a <= p (events i)) /\
      (!i j. i < n /\ j < n /\
             (i + 1 < j \/ j + 1 < i)
             ==> independent_events p (events i) (events j))
      ==> u n <= p {w:A | !i. i < n ==> w IN events i}`;;
