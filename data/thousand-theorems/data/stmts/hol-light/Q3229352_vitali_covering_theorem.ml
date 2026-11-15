(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3229352,
  "Vitali covering theorem": a fine family of closed sets in a second-countable
  pseudometric space, satisfying a uniform measure-growth bound, has a
  countable pairwise-disjoint subfamily covering the given set almost
  everywhere. This file contains no proof.
*)

let Q3229352_VITALI_COVERING_THEOREM =
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
   let emul =
      \(x:bool#real) (y:bool#real).
        if (~(FST x) /\ SND x = &0) \/
           (~(FST y) /\ SND y = &0)
        then ezero
        else if FST x \/ FST y
        then etop
        else (F,SND x * SND y) in
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
        events (UNIV:A->bool) /\
        (!s:A->bool.
           events s ==> events ((UNIV:A->bool) DIFF s)) /\
        (!sets:num->A->bool.
           (!n. events (sets n))
           ==> events {x:A | ?n. x IN sets n}) in
   let outer_measure =
      \(mu:(A->bool)->bool#real).
        (!s:A->bool. enonnegative (mu s)) /\
        mu {} = ezero /\
        (!s t:A->bool. s SUBSET t ==> ele (mu s) (mu t)) /\
        (!sets:num->A->bool.
           ?total:bool#real.
             esum (\n. mu (sets n)) total /\
             ele (mu {x:A | ?n. x IN sets n}) total) in
   let measure_space =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real).
        sigma_algebra events /\
        outer_measure mu /\
        (!s:A->bool.
           ?t:A->bool.
             events t /\
             s SUBSET t /\
             mu t = mu s) /\
        (!sets:num->A->bool.
           (!n. events (sets n)) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> esum (\n. mu (sets n))
                 (mu {x:A | ?n. x IN sets n})) in
   let is_pseudometric =
      \(d:A->A->real).
        (!x y:A. &0 <= d x y) /\
        (!x:A. d x x = &0) /\
        (!x y:A. d x y = d y x) /\
        (!x y z:A. d x z <= d x y + d y z) in
   let open_ball =
      \(d:A->A->real) (x:A) (radius:real).
        {y:A | d y x < radius} in
   let closed_ball =
      \(d:A->A->real) (x:A) (radius:real).
        {y:A | d y x <= radius} in
   let metric_open =
      \(d:A->A->real) (u:A->bool).
        !x:A.
          x IN u
          ==> ?radius:real.
                &0 < radius /\
                open_ball d x radius SUBSET u in
   let metric_closed =
      \(d:A->A->real) (s:A->bool).
        metric_open d ((UNIV:A->bool) DIFF s) in
   let interior_nonempty =
      \(d:A->A->real) (s:A->bool).
        ?x:A radius:real.
          &0 < radius /\
          open_ball d x radius SUBSET s in
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
   let locally_finite_measure =
      \(d:A->A->real) (mu:(A->bool)->bool#real).
        !x:A.
          ?u:A->bool.
            metric_open d u /\
            x IN u /\
            ~(FST (mu u)) in
   !d:A->A->real
    events:(A->bool)->bool
    mu:(A->bool)->bool#real
    s:A->bool
    t:J->bool
    C:real
    radius:J->real
    center:J->A
    B:J->A->bool.
      is_pseudometric d /\
      second_countable d /\
      measure_space events mu /\
      opens_measurable d events /\
      locally_finite_measure d mu /\
      &0 <= C /\
      (!a:J.
         a IN t
         ==> B a SUBSET closed_ball d (center a) (radius a)) /\
      (!a:J.
         a IN t
         ==> ele
               (mu (closed_ball d (center a) (&3 * radius a)))
               (emul (F,C) (mu (B a)))) /\
      (!a:J.
         a IN t
         ==> interior_nonempty d (B a)) /\
      (!a:J.
         a IN t
         ==> metric_closed d (B a)) /\
      (!x:A.
         x IN s
         ==> !epsilon:real.
               &0 < epsilon
               ==> ?a:J.
                     a IN t /\
                     radius a <= epsilon /\
                     center a = x)
      ==>
      ?u:J->bool.
        u SUBSET t /\
        COUNTABLE u /\
        (!a b:J.
           a IN u /\ b IN u /\ ~(a = b)
           ==> DISJOINT (B a) (B b)) /\
        mu
          (s DIFF
           {x:A |
              ?a:J.
                a IN u /\ x IN B a}) = ezero`;;
