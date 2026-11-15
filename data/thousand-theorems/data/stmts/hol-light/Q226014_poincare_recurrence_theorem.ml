(*
  Statement-only formalization of Thousand Theorems corpus artifact Q226014
  (thousand-theorems__hol-light__Q226014), "Poincare recurrence theorem":
  for a conservative nonsingular self-map of an arbitrary measure space,
  almost every point of a null-measurable set returns to it infinitely often.
  This file contains no proof.
*)

let Q226014_POINCARE_RECURRENCE_THEOREM =
 `let enonnegative =
      \(z:bool#real).
        (FST z /\ SND z = &0) \/
        (~(FST z) /\ &0 <= SND z) in
   let ezero = (F,&0) in
   let etop = (T,&0) in
   let ele =
      \(x:bool#real) (y:bool#real).
        FST y \/ (~(FST x) /\ SND x <= SND y) in
   let eadd =
      \(x:bool#real) (y:bool#real).
        if FST x \/ FST y
        then etop
        else (F,SND x + SND y) in
   let esup_sequence =
      \(u:num->bool#real) (z:bool#real).
        enonnegative z /\
        (!n. enonnegative (u n) /\ ele (u n) z) /\
        (!w. enonnegative w /\ (!n. ele (u n) w) ==> ele z w) in
   let esum =
      \(u:num->bool#real) (z:bool#real).
        ?partial:num->bool#real.
          partial 0 = ezero /\
          (!n. partial (SUC n) = eadd (partial n) (u n)) /\
          esup_sequence partial z in
   let sigma_algebra =
      \(events:(A->bool)->bool).
        events {} /\
        events (:A) /\
        (!u:A->bool.
           events u ==> events ((:A) DIFF u)) /\
        (!sets:num->A->bool.
           (!n. events (sets n))
           ==> events {x:A | ?n. x IN sets n}) in
   let measure_space =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real).
        sigma_algebra events /\
        (!u:A->bool. events u ==> enonnegative (mu u)) /\
        mu {} = ezero /\
        (!sets:num->A->bool.
           (!n. events (sets n)) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> esum
                 (\n. mu (sets n))
                 (mu {x:A | ?n. x IN sets n})) in
   let null_set =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real)
       (u:A->bool).
        ?z:A->bool.
          events z /\
          u SUBSET z /\
          mu z = ezero in
   let null_measurable_set =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real)
       (u:A->bool).
        ?v:A->bool.
          events v /\
          null_set events mu
            ((u DIFF v) UNION (v DIFF u)) in
   let measurable_map =
      \(events:(A->bool)->bool) (f:A->A).
        !u:A->bool.
          events u ==> events {x:A | f x IN u} in
   let quasi_measure_preserving =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real)
       (f:A->A).
        measurable_map events f /\
        (!u:A->bool.
           events u /\ mu u = ezero
           ==> mu {x:A | f x IN u} = ezero) in
   let conservative =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real)
       (f:A->A).
        quasi_measure_preserving events mu f /\
        (!u:A->bool.
           events u /\ ~(mu u = ezero)
           ==> ?x:A.
                 x IN u /\
                 ?m:num.
                   ~(m = 0) /\
                   ITER m f x IN u) in
   let frequently_at_top =
      \(p:num->bool).
        !N:num. ?n:num. N <= n /\ p n in
   let almost_everywhere =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real)
       (p:A->bool).
        null_set events mu {x:A | ~(p x)} in
   !events:(A->bool)->bool
    mu:(A->bool)->bool#real
    f:A->A
    s:A->bool.
      measure_space events mu /\
      conservative events mu f /\
      null_measurable_set events mu s
      ==>
      almost_everywhere events mu
        (\x:A.
           x IN s
           ==> frequently_at_top
                 (\n:num. ITER n f x IN s))`;;
