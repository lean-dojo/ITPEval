(*
  Statement-only formalization of Thousand Theorems corpus artifact Q137164,
  "Besicovitch covering theorem": in a second-countable metric space with the
  Besicovitch covering property, arbitrarily small admissible closed balls
  contain a countable pairwise-disjoint subfamily covering a given set almost
  everywhere for an s-finite measure. This file contains no proof.
*)

let Q137164_BESICOVITCH_COVERING_THEOREM =
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
   let outer_measure =
      \(mu:(A->bool)->bool#real).
        (!u:A->bool. enonnegative (mu u)) /\
        mu {} = ezero /\
        (!u v:A->bool.
           u SUBSET v ==> ele (mu u) (mu v)) /\
        (!sets:num->A->bool total:bool#real.
           esum (\n. mu (sets n)) total
           ==> ele (mu {x:A | ?n. x IN sets n}) total) in
   let measure_space =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real).
        sigma_algebra events /\
        outer_measure mu /\
        (!sets:num->A->bool.
           (!n. events (sets n)) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> esum (\n. mu (sets n))
                 (mu {x:A | ?n. x IN sets n})) in
   let sfinite_measure =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real).
        ?pieces:num->(A->bool)->bool#real.
          (!n. measure_space events (pieces n) /\
               ~(FST (pieces n (:A)))) /\
          (!u:A->bool.
             esum (\n. pieces n u) (mu u)) in
   let is_metric =
      \(d:A->A->real).
        (!x y:A. &0 <= d x y) /\
        (!x y:A. d x y = &0 <=> x = y) /\
        (!x y:A. d x y = d y x) /\
        (!x y z:A. d x z <= d x y + d y z) in
   let metric_open =
      \(d:A->A->real) (u:A->bool).
        !x:A.
          x IN u
          ==> ?epsilon:real.
                &0 < epsilon /\
                !y:A. d y x < epsilon ==> y IN u in
   let second_countable =
      \(d:A->A->real).
        ?basis:(A->bool)->bool.
          COUNTABLE basis /\
          (!b:A->bool. b IN basis ==> metric_open d b) /\
          (!u:A->bool x:A.
             metric_open d u /\ x IN u
             ==> ?b:A->bool.
                   b IN basis /\ x IN b /\ b SUBSET u) in
   let opens_measurable =
      \(d:A->A->real) (events:(A->bool)->bool).
        !u:A->bool. metric_open d u ==> events u in
   let satellite_configuration =
      \(d:A->A->real) (N:num) (tau:real)
       (c:num->A) (radius:num->real).
        (!i. i <= N ==> &0 < radius i) /\
        (!i j.
           i <= N /\ j <= N /\ ~(i = j)
           ==> (radius i <= d (c i) (c j) /\
                radius j <= tau * radius i) \/
               (radius j <= d (c j) (c i) /\
                radius i <= tau * radius j)) /\
        (!i.
           i < N
           ==> radius i <= d (c i) (c N) /\
               radius N <= tau * radius i) /\
        (!i.
           i < N
           ==> d (c i) (c N) <= radius i + radius N) in
   let has_besicovitch_covering =
      \(d:A->A->real).
        ?N:num tau:real.
          &1 < tau /\
          ~(?c:num->A radius:num->real.
              satellite_configuration d N tau c radius) in
   let closed_ball =
      \(d:A->A->real) (x:A) (radius:real).
        {y:A | d y x <= radius} in
   !d:A->A->real
    events:(A->bool)->bool
    mu:(A->bool)->bool#real
    f:A->real->bool
    s:A->bool
    R:A->real.
      is_metric d /\
      second_countable d /\
      measure_space events mu /\
      opens_measurable d events /\
      sfinite_measure events mu /\
      has_besicovitch_covering d /\
      (!x:A.
         x IN s
         ==> !delta:real.
               &0 < delta
               ==> ?radius:real.
                     f x radius /\
                     &0 < radius /\
                     radius < delta) /\
      (!x:A. x IN s ==> &0 < R x)
      ==>
      ?t:A->bool radius:A->real.
        COUNTABLE t /\
        t SUBSET s /\
        (!x:A.
           x IN t
           ==> f x (radius x) /\
               &0 < radius x /\
               radius x < R x) /\
        mu
          (s DIFF
           {y:A |
              ?x:A.
                x IN t /\
                y IN closed_ball d x (radius x)}) = ezero /\
        (!x y:A.
           x IN t /\ y IN t /\ ~(x = y)
           ==> DISJOINT
                 (closed_ball d x (radius x))
                 (closed_ball d y (radius y)))`;;
