(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3526996,
  "Kolmogorov extension theorem": a projective family of finite measures on
  the finite products of arbitrary Polish coordinate spaces has a measure on
  the full product with exactly those finite-dimensional marginals. This file
  contains no proof.
*)

let Q3526996_KOLMOGOROV_EXTENSION_THEOREM =
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
      \(space:(I->V)->bool)
       (events:((I->V)->bool)->bool).
        events {} /\
        events space /\
        (!s:(I->V)->bool. events s ==> s SUBSET space) /\
        (!s:(I->V)->bool.
           events s ==> events (space DIFF s)) /\
        (!sets:num->(I->V)->bool.
           (!n. events (sets n))
           ==> events {x:I->V | ?n:num. x IN sets n}) in
   let product_space =
      \(carrier:I->V->bool) (J:I->bool).
        {x:I->V | !i:I. i IN J ==> carrier i (x i)} in
   let metric_space_on =
      \(carrier:V->bool) (d:V->V->real).
        (!x y:V.
           x IN carrier /\ y IN carrier ==> &0 <= d x y) /\
        (!x y:V.
           x IN carrier /\ y IN carrier
           ==> (d x y = &0 <=> x = y)) /\
        (!x y:V.
           x IN carrier /\ y IN carrier
           ==> d x y = d y x) /\
        (!x y z:V.
           x IN carrier /\ y IN carrier /\ z IN carrier
           ==> d x z <= d x y + d y z) in
   let metric_open_on =
      \(carrier:V->bool) (d:V->V->real) (u:V->bool).
        u SUBSET carrier /\
        (!x:V.
           x IN u
           ==> ?epsilon:real.
                 &0 < epsilon /\
                 !y:V.
                   y IN carrier /\ d y x < epsilon
                   ==> y IN u) in
   let metric_tends_on =
      \(carrier:V->bool) (d:V->V->real)
       (u:num->V) (l:V).
        l IN carrier /\
        (!n:num. u n IN carrier) /\
        (!epsilon:real.
           &0 < epsilon
           ==> ?N:num.
                 !n:num.
                   N <= n ==> d (u n) l < epsilon) in
   let cauchy_on =
      \(carrier:V->bool) (d:V->V->real) (u:num->V).
        (!n:num. u n IN carrier) /\
        (!epsilon:real.
           &0 < epsilon
           ==> ?N:num.
                 !m n:num.
                   N <= m /\ N <= n
                   ==> d (u m) (u n) < epsilon) in
   let complete_on =
      \(carrier:V->bool) (d:V->V->real).
        !u:num->V.
          cauchy_on carrier d u
          ==> ?l:V. metric_tends_on carrier d u l in
   let second_countable_on =
      \(carrier:V->bool) (d:V->V->real).
        ?basis:(V->bool)->bool.
          COUNTABLE basis /\
          (!b:V->bool.
             b IN basis ==> metric_open_on carrier d b) /\
          (!u:V->bool x:V.
             metric_open_on carrier d u /\ x IN u
             ==> ?b:V->bool.
                   b IN basis /\ x IN b /\ b SUBSET u) in
   let polish_space_on =
      \(carrier:V->bool) (d:V->V->real).
        metric_space_on carrier d /\
        complete_on carrier d /\
        second_countable_on carrier d in
   let borel_events =
      \(carrier:V->bool) (d:V->V->real) (s:V->bool).
        !events:(V->bool)->bool.
          (events {} /\
           events carrier /\
           (!u:V->bool. events u ==> u SUBSET carrier) /\
           (!u:V->bool.
              events u ==> events (carrier DIFF u)) /\
           (!sets:num->V->bool.
              (!n. events (sets n))
              ==> events {x:V | ?n:num. x IN sets n})) /\
          (!u:V->bool.
             metric_open_on carrier d u ==> events u)
          ==> events s in
   let product_events =
      \(carrier:I->V->bool) (d:I->V->V->real)
       (J:I->bool) (s:(I->V)->bool).
        !events:((I->V)->bool)->bool.
          sigma_algebra (product_space carrier J) events /\
          (!i:I u:V->bool.
             i IN J /\ borel_events (carrier i) (d i) u
             ==> events
                   {x:I->V |
                      x IN product_space carrier J /\
                      x i IN u})
          ==> events s in
   let measure_space =
      \(space:(I->V)->bool)
       (events:((I->V)->bool)->bool)
       (mu:((I->V)->bool)->bool#real).
        sigma_algebra space events /\
        (!s:(I->V)->bool. enonnegative (mu s)) /\
        (!s:(I->V)->bool. mu s = mu (s INTER space)) /\
        mu {} = ezero /\
        (!sets:num->(I->V)->bool.
           (!n. events (sets n)) /\
           (!m n:num.
              ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> esum
                 (\n:num. mu (sets n))
                 (mu {x:I->V | ?n:num. x IN sets n})) in
   let finite_measure_space =
      \(space:(I->V)->bool)
       (events:((I->V)->bool)->bool)
       (mu:((I->V)->bool)->bool#real).
        measure_space space events mu /\
        ~(FST (mu space)) in
   let projective_measure_family =
      \(carrier:I->V->bool) (d:I->V->V->real)
       (P:(I->bool)->((I->V)->bool)->bool#real).
        (!J:I->bool.
           FINITE J
           ==> finite_measure_space
                 (product_space carrier J)
                 (product_events carrier d J)
                 (P J)) /\
        (!K J:I->bool s:(I->V)->bool.
           FINITE K /\
           FINITE J /\
           K SUBSET J /\
           product_events carrier d K s
           ==> P J (s INTER product_space carrier J) = P K s) in
   let is_projective_limit =
      \(carrier:I->V->bool) (d:I->V->V->real)
       (mu:((I->V)->bool)->bool#real)
       (P:(I->bool)->((I->V)->bool)->bool#real).
        measure_space
          (product_space carrier (:I))
          (product_events carrier d (:I))
          mu /\
        (!J:I->bool s:(I->V)->bool.
           FINITE J /\
           product_events carrier d J s
           ==> mu
                 (s INTER product_space carrier (:I)) =
               P J s) in
   let projective_limit =
      \(carrier:I->V->bool) (d:I->V->V->real)
       (P:(I->bool)->((I->V)->bool)->bool#real).
        @mu:((I->V)->bool)->bool#real.
          is_projective_limit carrier d mu P in
   !carrier:I->V->bool
    d:I->V->V->real
    P:(I->bool)->((I->V)->bool)->bool#real.
      (!i:I. polish_space_on (carrier i) (d i)) /\
      projective_measure_family carrier d P
      ==>
      is_projective_limit
        carrier d (projective_limit carrier d P) P`;;
