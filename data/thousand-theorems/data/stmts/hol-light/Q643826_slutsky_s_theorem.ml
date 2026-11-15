(*
  Statement-only formalization of Thousand Theorems corpus artifact Q643826,
  "Slutsky's theorem": a continuous function of random variables converging
  respectively in distribution and in probability to a constant converges in
  distribution to the corresponding continuous image. This file contains no
  proof.
*)

let q643826_real_tends = new_definition
 `q643826_real_tends (filter:(I->bool)->bool) (u:I->real) (z:real) <=>
    !epsilon:real.
      &0 < epsilon
      ==> filter {i:I | abs(u i - z) < epsilon}`;;

let q643826_sequence_tends = new_definition
 `q643826_sequence_tends (u:num->real) (z:real) <=>
    !epsilon:real.
      &0 < epsilon
      ==> ?N:num. !n:num. N <= n ==> abs(u n - z) < epsilon`;;

let q643826_is_filter = new_definition
 `q643826_is_filter (filter:(I->bool)->bool) <=>
    filter (:I) /\
    (!s t:I->bool. filter s /\ s SUBSET t ==> filter t) /\
    (!s t:I->bool. filter s /\ filter t ==> filter (s INTER t))`;;

let q643826_countably_generated_filter = new_definition
 `q643826_countably_generated_filter (filter:(I->bool)->bool) <=>
    ?base:num->I->bool.
      (!n:num. filter (base n)) /\
      (!s:I->bool. filter s <=> ?n:num. base n SUBSET s)`;;

let q643826_topology = new_definition
 `q643826_topology (opens:(A->bool)->bool) <=>
    opens {} /\
    opens (:A) /\
    (!collection:(A->bool)->bool.
       (!u:A->bool. u IN collection ==> opens u)
       ==> opens (UNIONS collection)) /\
    (!u v:A->bool. opens u /\ opens v ==> opens (u INTER v))`;;

let q643826_sigma_algebra = new_definition
 `q643826_sigma_algebra (events:(A->bool)->bool) <=>
    events {} /\
    events (:A) /\
    (!s:A->bool. events s ==> events ((:A) DIFF s)) /\
    (!sets:num->A->bool.
       (!n:num. events (sets n))
       ==> events {x:A | ?n:num. x IN sets n})`;;

let q643826_borel_space = new_definition
 `q643826_borel_space
    (opens:(A->bool)->bool) (events:(A->bool)->bool) <=>
    q643826_sigma_algebra events /\
    (!s:A->bool.
       events s <=>
       !candidate:(A->bool)->bool.
         q643826_sigma_algebra candidate /\
         (!u:A->bool. opens u ==> candidate u)
         ==> candidate s)`;;

let q643826_probability_measure = new_definition
 `q643826_probability_measure
    (events:(A->bool)->bool) (mu:(A->bool)->real) <=>
    q643826_sigma_algebra events /\
    mu {} = &0 /\
    mu (:A) = &1 /\
    (!s:A->bool. events s ==> &0 <= mu s) /\
    (!sets:num->A->bool.
       (!n:num. events (sets n)) /\
       (!m n:num. ~(m = n) ==> DISJOINT (sets m) (sets n))
       ==> q643826_sequence_tends
             (\N:num. sum {k:num | k < N} (\k. mu (sets k)))
             (mu {x:A | ?k:num. x IN sets k}))`;;

let q643826_outer_value = new_definition
 `q643826_outer_value
    (events:(A->bool)->bool) (mu:(A->bool)->real) (s:A->bool) =
    @r:real.
      (!t:A->bool. events t /\ s SUBSET t ==> r <= mu t) /\
      (!b:real.
         (!t:A->bool. events t /\ s SUBSET t ==> b <= mu t)
         ==> b <= r)`;;

let q643826_measurable = new_definition
 `q643826_measurable
    (eventsA:(A->bool)->bool) (eventsB:(B->bool)->bool) (f:A->B) <=>
    !s:B->bool. eventsB s ==> eventsA {x:A | f x IN s}`;;

let q643826_ae_equal = new_definition
 `q643826_ae_equal
    (events:(A->bool)->bool) (mu:(A->bool)->real)
    (f:A->B) (g:A->B) <=>
    ?null:A->bool.
      events null /\
      mu null = &0 /\
      {x:A | ~(f x = g x)} SUBSET null`;;

let q643826_ae_measurable = new_definition
 `q643826_ae_measurable
    (eventsA:(A->bool)->bool) (mu:(A->bool)->real)
    (eventsB:(B->bool)->bool) (f:A->B) <=>
    ?version:A->B.
      q643826_measurable eventsA eventsB version /\
      q643826_ae_equal eventsA mu f version`;;

let q643826_map_measure = new_definition
 `q643826_map_measure
    (eventsA:(A->bool)->bool) (mu:(A->bool)->real)
    (eventsB:(B->bool)->bool) (f:A->B)
    (law:(B->bool)->real) <=>
    q643826_probability_measure eventsB law /\
    ?version:A->B.
      q643826_measurable eventsA eventsB version /\
      q643826_ae_equal eventsA mu f version /\
      (!s:B->bool.
         eventsB s ==> law s = mu {x:A | version x IN s})`;;

let q643826_simple_nonnegative = new_definition
 `q643826_simple_nonnegative
    (events:(A->bool)->bool) (s:A->real) <=>
    (!x:A. &0 <= s x) /\
    FINITE (IMAGE s (:A)) /\
    (!c:real. events {x:A | s x = c})`;;

let q643826_simple_integral = new_definition
 `q643826_simple_integral
    (mu:(A->bool)->real) (s:A->real) =
    sum (IMAGE s (:A)) (\c:real. mu {x:A | s x = c} * c)`;;

let q643826_lintegral_upper = new_definition
 `q643826_lintegral_upper
    (events:(A->bool)->bool) (mu:(A->bool)->real)
    (h:A->real) (upper:real) <=>
    !s:A->real.
      q643826_simple_nonnegative events s /\
      (!x:A. s x <= h x)
      ==> q643826_simple_integral mu s <= upper`;;

let q643826_has_lintegral = new_definition
 `q643826_has_lintegral
    (events:(A->bool)->bool) (mu:(A->bool)->real)
    (h:A->real) (z:real) <=>
    &0 <= z /\
    q643826_lintegral_upper events mu h z /\
    (!upper:real.
       &0 <= upper /\
       q643826_lintegral_upper events mu h upper
       ==> z <= upper)`;;

let q643826_lintegral = new_definition
 `q643826_lintegral
    (events:(A->bool)->bool) (mu:(A->bool)->real) (h:A->real) =
    @z:real. q643826_has_lintegral events mu h z`;;

let q643826_integral = new_definition
 `q643826_integral
    (events:(A->bool)->bool) (mu:(A->bool)->real) (h:A->real) =
    q643826_lintegral events mu
      (\x:A. if &0 <= h x then h x else &0) -
    q643826_lintegral events mu
      (\x:A. if &0 <= --(h x) then --(h x) else &0)`;;

let q643826_real_open = new_definition
 `q643826_real_open (u:real->bool) <=>
    !x:real.
      x IN u
      ==> ?epsilon:real.
            &0 < epsilon /\
            !y:real. abs(y - x) < epsilon ==> y IN u`;;

let q643826_continuous_real = new_definition
 `q643826_continuous_real
    (opens:(A->bool)->bool) (h:A->real) <=>
    !u:real->bool.
      q643826_real_open u ==> opens {x:A | h x IN u}`;;

let q643826_bounded_continuous = new_definition
 `q643826_bounded_continuous
    (opens:(A->bool)->bool) (h:A->real) <=>
    q643826_continuous_real opens h /\
    ?bound:real. !x:A. abs(h x) <= bound`;;

let q643826_weak_tends = new_definition
 `q643826_weak_tends
    (opens:(A->bool)->bool) (events:(A->bool)->bool)
    (filter:(I->bool)->bool)
    (laws:I->(A->bool)->real) (limit:(A->bool)->real) <=>
    !h:A->real.
      q643826_bounded_continuous opens h
      ==> q643826_real_tends filter
            (\i:I. q643826_integral events (laws i) h)
            (q643826_integral events limit h)`;;

let q643826_tends_in_distribution = new_definition
 `q643826_tends_in_distribution
    (eventsA:(A->bool)->bool) (muA:(A->bool)->real)
    (eventsB:(B->bool)->bool) (muB:(B->bool)->real)
    (target_events:(C->bool)->bool)
    (target_opens:(C->bool)->bool)
    (X:I->A->C) (filter:(I->bool)->bool) (Z:B->C) <=>
    (!i:I.
       q643826_ae_measurable eventsA muA target_events (X i)) /\
    q643826_ae_measurable eventsB muB target_events Z /\
    ?laws:I->(C->bool)->real limit_law:(C->bool)->real.
      (!i:I.
         q643826_map_measure
           eventsA muA target_events (X i) (laws i)) /\
      q643826_map_measure
        eventsB muB target_events Z limit_law /\
      q643826_weak_tends
        target_opens target_events filter laws limit_law`;;

let q643826_seminormed_add_comm_group = new_definition
 `q643826_seminormed_add_comm_group
    (zero:A) (add:A->A->A) (neg:A->A) (norm:A->real) <=>
    (!x y z:A. add x (add y z) = add (add x y) z) /\
    (!x y:A. add x y = add y x) /\
    (!x:A. add zero x = x) /\
    (!x:A. add (neg x) x = zero) /\
    norm zero = &0 /\
    (!x:A. &0 <= norm x) /\
    (!x:A. norm (neg x) = norm x) /\
    (!x y:A. norm (add x y) <= norm x + norm y)`;;

let q643826_norm_open = new_definition
 `q643826_norm_open
    (add:A->A->A) (neg:A->A) (norm:A->real) (u:A->bool) <=>
    !x:A.
      x IN u
      ==> ?epsilon:real.
            &0 < epsilon /\
            !y:A. norm (add y (neg x)) < epsilon ==> y IN u`;;

let q643826_second_countable_norm = new_definition
 `q643826_second_countable_norm
    (add:A->A->A) (neg:A->A) (norm:A->real) <=>
    ?basis:num->A->bool.
      (!n:num. q643826_norm_open add neg norm (basis n)) /\
      (!u:A->bool.
         q643826_norm_open add neg norm u
         ==> !x:A.
               x IN u
               ==> ?n:num.
                     x IN basis n /\ basis n SUBSET u)`;;

let q643826_continuous_prod = new_definition
 `q643826_continuous_prod
    (addA:A->A->A) (negA:A->A) (normA:A->real)
    (addB:B->B->B) (negB:B->B) (normB:B->real)
    (opensC:(C->bool)->bool) (g:A#B->C) <=>
    !x:A y:B u:C->bool.
      opensC u /\ g (x,y) IN u
      ==> ?epsilon:real.
            &0 < epsilon /\
            !x':A y':B.
              normA (addA x' (negA x)) < epsilon /\
              normB (addB y' (negB y)) < epsilon
              ==> g (x',y') IN u`;;

let q643826_tends_in_measure_const = new_definition
 `q643826_tends_in_measure_const
    (events:(A->bool)->bool) (mu:(A->bool)->real)
    (add:B->B->B) (neg:B->B) (norm:B->real)
    (Y:I->A->B) (filter:(I->bool)->bool) (c:B) <=>
    !epsilon:real.
      &0 < epsilon
      ==> q643826_real_tends filter
            (\i:I.
               q643826_outer_value events mu
                 {x:A |
                    epsilon <= norm (add (Y i x) (neg c))})
            (&0)`;;

let Q643826_SLUTSKYS_THEOREM =
 `!eventsO:(O->bool)->bool
    muO:(O->bool)->real
    eventsL:(L->bool)->bool
    muL:(L->bool)->real
    eventsE:(E->bool)->bool
    eventsP:(P->bool)->bool
    opensF:(F->bool)->bool
    eventsF:(F->bool)->bool
    filter:(I->bool)->bool
    zeroE:E
    addE:E->E->E
    negE:E->E
    normE:E->real
    zeroP:P
    addP:P->P->P
    negP:P->P
    normP:P->real
    X:I->O->E
    Y:I->O->P
    Z:L->E
    c:P
    g:E#P->F.
      q643826_probability_measure eventsO muO /\
      q643826_probability_measure eventsL muL /\
      q643826_seminormed_add_comm_group
        zeroE addE negE normE /\
      q643826_seminormed_add_comm_group
        zeroP addP negP normP /\
      q643826_second_countable_norm addE negE normE /\
      q643826_second_countable_norm addP negP normP /\
      q643826_borel_space
        (q643826_norm_open addE negE normE) eventsE /\
      q643826_borel_space
        (q643826_norm_open addP negP normP) eventsP /\
      q643826_topology opensF /\
      q643826_borel_space opensF eventsF /\
      q643826_is_filter filter /\
      q643826_countably_generated_filter filter /\
      q643826_continuous_prod
        addE negE normE addP negP normP opensF g /\
      q643826_tends_in_distribution
        eventsO muO eventsL muL
        eventsE (q643826_norm_open addE negE normE)
        X filter Z /\
      q643826_tends_in_measure_const
        eventsO muO addP negP normP Y filter c /\
      (!i:I.
         q643826_ae_measurable eventsO muO eventsP (Y i))
      ==>
      q643826_tends_in_distribution
        eventsO muO eventsL muL eventsF opensF
        (\i:I x:O. g (X i x,Y i x))
        filter
        (\x:L. g (Z x,c))`;;
