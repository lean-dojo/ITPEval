(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1568811,
  "Hahn decomposition theorem": every real signed measure on an arbitrary
  measurable space has complementary measurable positive and negative sets.
  This file contains no proof.
*)

let Q1568811_HAHN_DECOMPOSITION_THEOREM =
 `let scalar_tends =
      \(u:num->real) (l:real).
        !e. &0 < e
            ==> ?N. !n. N <= n ==> abs(u n - l) < e in
   let sigma_algebra =
      \(events:(A->bool)->bool).
        events {} /\
        events (:A) /\
        (!s:A->bool.
           events s ==> events ((:A) DIFF s)) /\
        (!sets:num->A->bool.
           (!n. events (sets n))
           ==> events {x:A | ?n. x IN sets n}) in
   let signed_measure =
      \(events:(A->bool)->bool) (mu:(A->bool)->real).
        sigma_algebra events /\
        mu {} = &0 /\
        (!s:A->bool. ~(events s) ==> mu s = &0) /\
        (!sets:num->A->bool.
           (!n. events (sets n)) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> ?partial:num->real.
                 partial 0 = &0 /\
                 (!n. partial (SUC n) =
                      partial n + mu (sets n)) /\
                 scalar_tends partial
                   (mu {x:A | ?n. x IN sets n})) in
   let positive_set =
      \(events:(A->bool)->bool) (mu:(A->bool)->real)
       (i:A->bool).
        !t:A->bool.
          events t /\ t SUBSET i ==> &0 <= mu t in
   let negative_set =
      \(events:(A->bool)->bool) (mu:(A->bool)->real)
       (j:A->bool).
        !t:A->bool.
          events t /\ t SUBSET j ==> mu t <= &0 in
   !events:(A->bool)->bool mu:(A->bool)->real.
      signed_measure events mu
      ==> ?i j:A->bool.
            events i /\
            positive_set events mu i /\
            events j /\
            negative_set events mu j /\
            DISJOINT i j /\
            i UNION j = (:A)`;;
