(*
  Statement-only formalization of Thousand Theorems corpus artifact Q7432915,
  (thousand-theorems__hol-light__Q7432915), "Schroeder–Bernstein theorem for
  measurable spaces": measurable embeddings in both directions between two
  possibly empty measurable spaces imply a measurable equivalence. This file
  contains no proof.
*)

let Q7432915_SCHROEDER_BERNSTEIN_THEOREM_FOR_MEASURABLE_SPACES =
 `let sigma_algebraA =
      \(carrier:A->bool) (events:(A->bool)->bool).
        events {} /\
        events carrier /\
        (!s:A->bool. events s ==> s SUBSET carrier) /\
        (!s:A->bool.
           events s ==> events (carrier DIFF s)) /\
        (!sets:num->A->bool.
           (!n. events (sets n))
           ==> events {x:A | ?n. x IN sets n}) in
   let sigma_algebraB =
      \(carrier:B->bool) (events:(B->bool)->bool).
        events {} /\
        events carrier /\
        (!s:B->bool. events s ==> s SUBSET carrier) /\
        (!s:B->bool.
           events s ==> events (carrier DIFF s)) /\
        (!sets:num->B->bool.
           (!n. events (sets n))
           ==> events {y:B | ?n. y IN sets n}) in
   let measurableAB =
      \(carrierA:A->bool) (eventsA:(A->bool)->bool)
       (carrierB:B->bool) (eventsB:(B->bool)->bool)
       (f:A->B).
        (!x:A. x IN carrierA ==> f x IN carrierB) /\
        (!t:B->bool.
           eventsB t
           ==> eventsA {x:A | x IN carrierA /\ f x IN t}) in
   let measurableBA =
      \(carrierB:B->bool) (eventsB:(B->bool)->bool)
       (carrierA:A->bool) (eventsA:(A->bool)->bool)
       (g:B->A).
        (!y:B. y IN carrierB ==> g y IN carrierA) /\
        (!s:A->bool.
           eventsA s
           ==> eventsB {y:B | y IN carrierB /\ g y IN s}) in
   let measurable_embeddingAB =
      \(carrierA:A->bool) (eventsA:(A->bool)->bool)
       (carrierB:B->bool) (eventsB:(B->bool)->bool)
       (f:A->B).
        measurableAB carrierA eventsA carrierB eventsB f /\
        (!x y:A.
           x IN carrierA /\ y IN carrierA /\ f x = f y
           ==> x = y) /\
        (!s:A->bool.
           eventsA s
           ==> eventsB {y:B | ?x:A. x IN s /\ f x = y}) in
   let measurable_embeddingBA =
      \(carrierB:B->bool) (eventsB:(B->bool)->bool)
       (carrierA:A->bool) (eventsA:(A->bool)->bool)
       (g:B->A).
        measurableBA carrierB eventsB carrierA eventsA g /\
        (!x y:B.
           x IN carrierB /\ y IN carrierB /\ g x = g y
           ==> x = y) /\
        (!s:B->bool.
           eventsB s
           ==> eventsA {x:A | ?y:B. y IN s /\ g y = x}) in
   !carrierA:A->bool carrierB:B->bool
    eventsA:(A->bool)->bool eventsB:(B->bool)->bool
    f:A->B g:B->A.
      sigma_algebraA carrierA eventsA /\
      sigma_algebraB carrierB eventsB /\
      measurable_embeddingAB carrierA eventsA carrierB eventsB f /\
      measurable_embeddingBA carrierB eventsB carrierA eventsA g
      ==>
      ?h:A->B k:B->A.
        measurableAB carrierA eventsA carrierB eventsB h /\
        measurableBA carrierB eventsB carrierA eventsA k /\
        (!x:A. x IN carrierA ==> k (h x) = x) /\
        (!y:B. y IN carrierB ==> h (k y) = y)`;;
