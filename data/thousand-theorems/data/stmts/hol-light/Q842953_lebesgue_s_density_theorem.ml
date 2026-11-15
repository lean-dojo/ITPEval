(*
  Statement-only formalization of Thousand Theorems corpus artifact Q842953,
  thousand-theorems__hol-light__Q842953, "Lebesgue's density theorem": in a
  second-countable Borel metric space with the Besicovitch covering property,
  almost every point of an arbitrary set has closed-ball measure density
  tending to one for a locally finite measure. This file contains no proof.
*)

let Q842953_LEBESGUE_S_DENSITY_THEOREM =
 `let enonnegative =
      \(z:bool#real).
        (FST z /\ SND z = &0) \/
        (~(FST z) /\ &0 <= SND z) in
   let ezero = (F,&0) in
   let eone = (F,&1) in
   let etop = (T,&0) in
   let ele =
      \(x:bool#real) (y:bool#real).
        FST y \/ (~(FST x) /\ SND x <= SND y) in
   let eadd =
      \(x:bool#real) (y:bool#real).
        if FST x \/ FST y
        then etop
        else (F,SND x + SND y) in
   let emul =
      \(x:bool#real) (y:bool#real).
        if (~(FST x) /\ SND x = &0) \/
           (~(FST y) /\ SND y = &0)
        then ezero
        else if FST x \/ FST y
        then etop
        else (F,SND x * SND y) in
   let einv =
      \(x:bool#real).
        if FST x
        then ezero
        else if SND x = &0
        then etop
        else (F,&1 / SND x) in
   let ediv =
      \(x:bool#real) (y:bool#real). emul x (einv y) in
   let eembed =
      \(z:bool#real).
        if FST z then &1 else SND z / (&1 + SND z) in
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
      \(carrier:A->bool) (events:(A->bool)->bool).
        events {} /\
        events carrier /\
        (!u:A->bool. events u ==> u SUBSET carrier) /\
        (!u:A->bool.
           events u ==> events (carrier DIFF u)) /\
        (!sets:num->A->bool.
           (!n. events (sets n))
           ==> events
                 {x:A |
                    x IN carrier /\ ?n:num. x IN sets n}) in
   let outer_measure =
      \(carrier:A->bool) (mu:(A->bool)->bool#real).
        (!u:A->bool. enonnegative (mu u)) /\
        (!u:A->bool. mu u = mu (u INTER carrier)) /\
        mu {} = ezero /\
        (!u v:A->bool.
           u SUBSET v ==> ele (mu u) (mu v)) /\
        (!sets:num->A->bool total:bool#real.
           esum (\n. mu (sets n)) total
           ==> ele
                 (mu {x:A | x IN carrier /\ ?n:num. x IN sets n})
                 total) in
   let measure_space =
      \(carrier:A->bool)
       (events:(A->bool)->bool)
       (mu:(A->bool)->bool#real).
        sigma_algebra carrier events /\
        outer_measure carrier mu /\
        (!u:A->bool.
           u SUBSET carrier
           ==> (!v:A->bool.
                  events v /\ u SUBSET v
                  ==> ele (mu u) (mu v)) /\
               (!w:bool#real.
                  enonnegative w /\
                  (!v:A->bool.
                     events v /\ u SUBSET v
                     ==> ele w (mu v))
                  ==> ele w (mu u))) /\
        (!sets:num->A->bool.
           (!n. events (sets n)) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> esum
                 (\n. mu (sets n))
                 (mu {x:A |
                        x IN carrier /\ ?n:num. x IN sets n})) in
   let is_metric =
      \(carrier:A->bool) (d:A->A->real).
        (!x y:A.
           x IN carrier /\ y IN carrier ==> &0 <= d x y) /\
        (!x y:A.
           x IN carrier /\ y IN carrier
           ==> (d x y = &0 <=> x = y)) /\
        (!x y:A.
           x IN carrier /\ y IN carrier ==> d x y = d y x) /\
        (!x y z:A.
           x IN carrier /\ y IN carrier /\ z IN carrier
           ==> d x z <= d x y + d y z) in
   let open_ball =
      \(carrier:A->bool) (d:A->A->real)
       (x:A) (radius:real).
        {y:A | y IN carrier /\ d y x < radius} in
   let closed_ball =
      \(carrier:A->bool) (d:A->A->real)
       (x:A) (radius:real).
        {y:A | y IN carrier /\ d y x <= radius} in
   let metric_open =
      \(carrier:A->bool) (d:A->A->real) (u:A->bool).
        u SUBSET carrier /\
        !x:A.
          x IN u
          ==> ?radius:real.
                &0 < radius /\
                open_ball carrier d x radius SUBSET u in
   let second_countable =
      \(carrier:A->bool) (d:A->A->real).
        ?basis:(A->bool)->bool.
          COUNTABLE basis /\
          (!b:A->bool.
             b IN basis ==> metric_open carrier d b) /\
          (!u:A->bool x:A.
             metric_open carrier d u /\ x IN u
             ==> ?b:A->bool.
                   b IN basis /\ x IN b /\ b SUBSET u) in
   let borel_space =
      \(carrier:A->bool) (d:A->A->real)
       (events:(A->bool)->bool).
        sigma_algebra carrier events /\
        (!u:A->bool.
           metric_open carrier d u ==> events u) /\
        (!other:(A->bool)->bool.
           sigma_algebra carrier other /\
           (!u:A->bool.
              metric_open carrier d u ==> other u)
           ==> !u:A->bool. events u ==> other u) in
   let locally_finite_measure =
      \(carrier:A->bool) (d:A->A->real)
       (mu:(A->bool)->bool#real).
        !x:A.
          x IN carrier
          ==> ?u:A->bool.
                metric_open carrier d u /\
                x IN u /\
                ~(FST (mu u)) in
   let satellite_configuration =
      \(carrier:A->bool) (d:A->A->real)
       (N:num) (tau:real)
       (c:num->A) (radius:num->real).
        (!i:num.
           i <= N ==> c i IN carrier /\ &0 < radius i) /\
        (!i j:num.
           i <= N /\ j <= N /\ ~(i = j)
           ==> (radius i <= d (c i) (c j) /\
                radius j <= tau * radius i) \/
               (radius j <= d (c j) (c i) /\
                radius i <= tau * radius j)) /\
        (!i:num.
           i < N
           ==> radius i <= d (c i) (c N) /\
               radius N <= tau * radius i) /\
        (!i:num.
           i < N
           ==> d (c i) (c N) <= radius i + radius N) in
   let has_besicovitch_covering =
      \(carrier:A->bool) (d:A->A->real).
        ?N:num tau:real.
          &1 < tau /\
          ~(?c:num->A radius:num->real.
              satellite_configuration
                carrier d N tau c radius) in
   let density_tends_to_one =
      \(carrier:A->bool) (d:A->A->real)
       (mu:(A->bool)->bool#real)
       (s:A->bool) (x:A).
        !epsilon:real.
          &0 < epsilon
          ==> ?delta:real.
                &0 < delta /\
                !radius:real.
                  &0 < radius /\ radius < delta
                  ==> abs
                        (eembed
                          (ediv
                            (mu
                              (s INTER
                               closed_ball
                                 carrier d x radius))
                            (mu
                              (closed_ball
                                carrier d x radius))) -
                         eembed eone) < epsilon in
   let almost_everywhere_restrict =
      \(carrier:A->bool)
       (events:(A->bool)->bool)
       (mu:(A->bool)->bool#real)
       (s:A->bool) (p:A->bool).
        ?null_set:A->bool.
          events null_set /\
          {x:A | x IN carrier /\ ~(p x)} SUBSET null_set /\
          mu (null_set INTER s) = ezero in
   !carrier:A->bool
    d:A->A->real
    events:(A->bool)->bool
    mu:(A->bool)->bool#real
    s:A->bool.
      is_metric carrier d /\
      second_countable carrier d /\
      borel_space carrier d events /\
      measure_space carrier events mu /\
      locally_finite_measure carrier d mu /\
      has_besicovitch_covering carrier d /\
      s SUBSET carrier
      ==>
      almost_everywhere_restrict carrier events mu s
        (\x:A. density_tends_to_one carrier d mu s x)`;;
