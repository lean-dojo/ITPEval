(*
  Statement-only formalization of Thousand Theorems corpus artifact Q966837
  (thousand-theorems__hol-light__Q966837), "Cramér–Wold theorem":
  convergence in distribution of finite-dimensional real inner-product-space
  valued random variables is equivalent to convergence in distribution of
  every scalar inner-product projection. This file contains no proof.
*)

let q966837_sequence_tends = new_definition
 `q966837_sequence_tends (u:num->real) (z:real) <=>
    !epsilon:real.
      &0 < epsilon
      ==> ?N:num. !n:num. N <= n ==> abs(u n - z) < epsilon`;;

let q966837_sigma_algebra = new_definition
 `q966837_sigma_algebra (events:(A->bool)->bool) <=>
    events {} /\
    events (:A) /\
    (!s:A->bool. events s ==> events ((:A) DIFF s)) /\
    (!sets:num->A->bool.
       (!n:num. events (sets n))
       ==> events {x:A | ?n:num. x IN sets n})`;;

let q966837_probability_measure = new_definition
 `q966837_probability_measure
    (events:(A->bool)->bool) (mu:(A->bool)->real) <=>
    q966837_sigma_algebra events /\
    mu {} = &0 /\
    mu (:A) = &1 /\
    (!s:A->bool. events s ==> &0 <= mu s) /\
    (!sets:num->A->bool.
       (!n:num. events (sets n)) /\
       (!m n:num. ~(m = n) ==> DISJOINT (sets m) (sets n))
       ==> q966837_sequence_tends
             (\N:num. sum {k:num | k < N} (\k. mu (sets k)))
             (mu {x:A | ?k:num. x IN sets k}))`;;

let q966837_borel_event = new_definition
 `q966837_borel_event
    (opens:(A->bool)->bool) (s:A->bool) <=>
    !events:(A->bool)->bool.
      q966837_sigma_algebra events /\
      (!u:A->bool. opens u ==> events u)
      ==> events s`;;

let q966837_borel_space = new_definition
 `q966837_borel_space
    (opens:(A->bool)->bool) (events:(A->bool)->bool) <=>
    !s:A->bool. events s <=> q966837_borel_event opens s`;;

let q966837_measurable = new_definition
 `q966837_measurable
    (eventsA:(A->bool)->bool) (eventsB:(B->bool)->bool)
    (f:A->B) <=>
    !s:B->bool. eventsB s ==> eventsA {x:A | f x IN s}`;;

let q966837_ae_equal = new_definition
 `q966837_ae_equal
    (events:(A->bool)->bool) (mu:(A->bool)->real)
    (f:A->B) (g:A->B) <=>
    ?null:A->bool.
      events null /\
      mu null = &0 /\
      {x:A | ~(f x = g x)} SUBSET null`;;

let q966837_ae_measurable = new_definition
 `q966837_ae_measurable
    (eventsA:(A->bool)->bool) (mu:(A->bool)->real)
    (eventsB:(B->bool)->bool) (f:A->B) <=>
    ?version:A->B.
      q966837_measurable eventsA eventsB version /\
      q966837_ae_equal eventsA mu f version`;;

let q966837_map_measure = new_definition
 `q966837_map_measure
    (eventsA:(A->bool)->bool) (mu:(A->bool)->real)
    (eventsB:(B->bool)->bool) (f:A->B)
    (law:(B->bool)->real) <=>
    q966837_probability_measure eventsB law /\
    ?version:A->B.
      q966837_measurable eventsA eventsB version /\
      q966837_ae_equal eventsA mu f version /\
      (!s:B->bool.
         eventsB s ==> law s = mu {x:A | version x IN s})`;;

let q966837_simple_nonnegative = new_definition
 `q966837_simple_nonnegative
    (events:(A->bool)->bool) (s:A->real) <=>
    (!x:A. &0 <= s x) /\
    FINITE (IMAGE s (:A)) /\
    (!c:real. events {x:A | s x = c})`;;

let q966837_simple_integral = new_definition
 `q966837_simple_integral
    (mu:(A->bool)->real) (s:A->real) =
    sum (IMAGE s (:A)) (\c:real. mu {x:A | s x = c} * c)`;;

let q966837_lintegral_upper = new_definition
 `q966837_lintegral_upper
    (events:(A->bool)->bool) (mu:(A->bool)->real)
    (h:A->real) (upper:real) <=>
    !s:A->real.
      q966837_simple_nonnegative events s /\
      (!x:A. s x <= h x)
      ==> q966837_simple_integral mu s <= upper`;;

let q966837_has_lintegral = new_definition
 `q966837_has_lintegral
    (events:(A->bool)->bool) (mu:(A->bool)->real)
    (h:A->real) (z:real) <=>
    &0 <= z /\
    q966837_lintegral_upper events mu h z /\
    (!upper:real.
       &0 <= upper /\
       q966837_lintegral_upper events mu h upper
       ==> z <= upper)`;;

let q966837_lintegral = new_definition
 `q966837_lintegral
    (events:(A->bool)->bool) (mu:(A->bool)->real) (h:A->real) =
    @z:real. q966837_has_lintegral events mu h z`;;

let q966837_integral = new_definition
 `q966837_integral
    (events:(A->bool)->bool) (mu:(A->bool)->real) (h:A->real) =
    q966837_lintegral events mu
      (\x:A. if &0 <= h x then h x else &0) -
    q966837_lintegral events mu
      (\x:A. if h x < &0 then --(h x) else &0)`;;

let q966837_real_open = new_definition
 `q966837_real_open (u:real->bool) <=>
    !x:real.
      x IN u
      ==> ?epsilon:real.
            &0 < epsilon /\
            !y:real. abs(y - x) < epsilon ==> y IN u`;;

let q966837_continuous_real = new_definition
 `q966837_continuous_real
    (opens:(A->bool)->bool) (h:A->real) <=>
    !u:real->bool.
      q966837_real_open u ==> opens {x:A | h x IN u}`;;

let q966837_bounded_continuous = new_definition
 `q966837_bounded_continuous
    (opens:(A->bool)->bool) (h:A->real) <=>
    q966837_continuous_real opens h /\
    ?bound:real. !x:A. abs(h x) <= bound`;;

let q966837_weak_tends = new_definition
 `q966837_weak_tends
    (opens:(A->bool)->bool) (events:(A->bool)->bool)
    (laws:num->(A->bool)->real) (limit:(A->bool)->real) <=>
    !h:A->real.
      q966837_bounded_continuous opens h
      ==> q966837_sequence_tends
            (\n:num. q966837_integral events (laws n) h)
            (q966837_integral events limit h)`;;

let q966837_tends_in_distribution = new_definition
 `q966837_tends_in_distribution
    (eventsO:(O->bool)->bool) (muO:(O->bool)->real)
    (eventsL:(L->bool)->bool) (muL:(L->bool)->real)
    (target_events:(E->bool)->bool)
    (target_opens:(E->bool)->bool)
    (X:num->O->E) (Z:L->E) <=>
    (!n:num.
       q966837_ae_measurable eventsO muO target_events (X n)) /\
    q966837_ae_measurable eventsL muL target_events Z /\
    ?laws:num->(E->bool)->real limit_law:(E->bool)->real.
      (!n:num.
         q966837_map_measure
           eventsO muO target_events (X n) (laws n)) /\
      q966837_map_measure
        eventsL muL target_events Z limit_law /\
      q966837_weak_tends
        target_opens target_events laws limit_law`;;

let q966837_real_inner_product_space = new_definition
 `q966837_real_inner_product_space
    (zero:E) (add:E->E->E) (neg:E->E)
    (smul:real->E->E) (inner:E->E->real) (norm:E->real) <=>
    (!x y z:E. add x (add y z) = add (add x y) z) /\
    (!x y:E. add x y = add y x) /\
    (!x:E. add zero x = x) /\
    (!x:E. add (neg x) x = zero) /\
    (!x:E. smul (&1) x = x) /\
    (!x:E. smul (&0) x = zero) /\
    (!a:real. smul a zero = zero) /\
    (!a b:real. !x:E. smul (a * b) x = smul a (smul b x)) /\
    (!a b:real. !x:E.
       smul (a + b) x = add (smul a x) (smul b x)) /\
    (!a:real. !x y:E.
       smul a (add x y) = add (smul a x) (smul a y)) /\
    (!x y:E. inner x y = inner y x) /\
    (!x y z:E. inner (add x y) z = inner x z + inner y z) /\
    (!a:real. !x y:E. inner (smul a x) y = a * inner x y) /\
    (!x:E. &0 <= inner x x) /\
    (!x:E. inner x x = &0 <=> x = zero) /\
    (!x:E. norm x = sqrt(inner x x))`;;

let q966837_finite_dimensional = new_definition
 `q966837_finite_dimensional
    (zero:E) (add:E->E->E) (smul:real->E->E) <=>
    ?d:num basis:num->E.
      !x:E.
        ?coeff:num->real partial:num->E.
          partial 0 = zero /\
          (!i:num.
             i < d
             ==> partial (SUC i) =
                 add (partial i) (smul (coeff i) (basis i))) /\
          partial d = x`;;

let q966837_norm_open = new_definition
 `q966837_norm_open
    (add:E->E->E) (neg:E->E) (norm:E->real) (u:E->bool) <=>
    !x:E.
      x IN u
      ==> ?epsilon:real.
            &0 < epsilon /\
            !y:E.
              norm (add y (neg x)) < epsilon ==> y IN u`;;

let Q966837_CRAMER_WOLD_THEOREM =
 `!eventsO:(O->bool)->bool
    muO:(O->bool)->real
    eventsL:(L->bool)->bool
    muL:(L->bool)->real
    eventsE:(E->bool)->bool
    zero:E
    add:E->E->E
    neg:E->E
    smul:real->E->E
    inner:E->E->real
    norm:E->real
    X:num->O->E
    Z:L->E.
      q966837_probability_measure eventsO muO /\
      q966837_probability_measure eventsL muL /\
      q966837_real_inner_product_space
        zero add neg smul inner norm /\
      q966837_finite_dimensional zero add smul /\
      q966837_borel_space
        (q966837_norm_open add neg norm) eventsE /\
      (!n:num.
         q966837_ae_measurable eventsO muO eventsE (X n)) /\
      q966837_ae_measurable eventsL muL eventsE Z
      ==>
      (q966837_tends_in_distribution
         eventsO muO eventsL muL eventsE
         (q966837_norm_open add neg norm) X Z
       <=>
       !t:E.
         q966837_tends_in_distribution
           eventsO muO eventsL muL
           (q966837_borel_event q966837_real_open)
           q966837_real_open
           (\n:num x:O. inner (X n x) t)
           (\x:L. inner (Z x) t))`;;
