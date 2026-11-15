(*
  Statement-only formalization of Thousand Theorems corpus artifact Q7249519,
  "Prokhorov's theorem": on an arbitrary possibly empty Hausdorff Borel space,
  finite measures of bounded mass whose masses outside a sequence of compact
  sets are bounded by a nonnegative sequence tending to zero form a compact
  set in the weak topology, provided the space is normal or the compact sets
  are monotone. This file contains no proof.
*)

let Q7249519_PROKHOROVS_THEOREM =
 `let sequence_tends =
      \(a:num->real) (l:real).
        !epsilon:real.
          &0 < epsilon
          ==> ?N:num.
                !n:num. N <= n ==> abs(a n - l) < epsilon in
   let topology =
      \(carrier:A->bool) (opens:(A->bool)->bool).
        opens {} /\
        opens carrier /\
        (!u:A->bool. opens u ==> u SUBSET carrier) /\
        (!collection:(A->bool)->bool.
           (!u:A->bool. u IN collection ==> opens u)
           ==> opens (UNIONS collection)) /\
        (!u v:A->bool.
           opens u /\ opens v ==> opens (u INTER v)) in
   let closed_set =
      \(carrier:A->bool) (opens:(A->bool)->bool) (s:A->bool).
        s SUBSET carrier /\ opens (carrier DIFF s) in
   let compact_set =
      \(carrier:A->bool) (opens:(A->bool)->bool) (s:A->bool).
        s SUBSET carrier /\
        !cover:(A->bool)->bool.
          (!u:A->bool. u IN cover ==> opens u) /\
          s SUBSET UNIONS cover
          ==> ?subcover:(A->bool)->bool.
                subcover SUBSET cover /\
                FINITE subcover /\
                s SUBSET UNIONS subcover in
   let hausdorff_space =
      \(carrier:A->bool) (opens:(A->bool)->bool).
        !x y:A.
          x IN carrier /\
          y IN carrier /\
          ~(x = y)
          ==> ?u v:A->bool.
                opens u /\
                opens v /\
                x IN u /\
                y IN v /\
                DISJOINT u v in
   let normal_space =
      \(carrier:A->bool) (opens:(A->bool)->bool).
        !s t:A->bool.
          closed_set carrier opens s /\
          closed_set carrier opens t /\
          DISJOINT s t
          ==> ?u v:A->bool.
                opens u /\
                opens v /\
                s SUBSET u /\
                t SUBSET v /\
                DISJOINT u v in
   let sigma_algebra =
      \(carrier:A->bool) (events:(A->bool)->bool).
        events {} /\
        events carrier /\
        (!s:A->bool. events s ==> s SUBSET carrier) /\
        (!s:A->bool.
           events s ==> events (carrier DIFF s)) /\
        (!sets:num->A->bool.
           (!n:num. events (sets n))
           ==> events {x:A | ?n:num. x IN sets n}) in
   let borel_space =
      \(carrier:A->bool)
       (opens:(A->bool)->bool) (events:(A->bool)->bool).
        sigma_algebra carrier events /\
        (!u:A->bool. opens u ==> events u) /\
        (!candidate:(A->bool)->bool.
           sigma_algebra carrier candidate /\
           (!u:A->bool. opens u ==> candidate u)
           ==> !s:A->bool. events s ==> candidate s) in
   let finite_measure =
      \(carrier:A->bool)
       (events:(A->bool)->bool) (mu:(A->bool)->real).
        sigma_algebra carrier events /\
        mu {} = &0 /\
        (!s:A->bool. &0 <= mu s) /\
        (!s:A->bool. ~(events s) ==> mu s = &0) /\
        (!sets:num->A->bool.
           (!n:num. events (sets n)) /\
           (!m n:num. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> sequence_tends
                 (\N:num. sum {k:num | k < N} (\k. mu (sets k)))
                 (mu {x:A | ?k:num. x IN sets k})) in
   let real_open =
      \(v:real->bool).
        !x:real.
          x IN v
          ==> ?epsilon:real.
                &0 < epsilon /\
                !y:real. abs(y - x) < epsilon ==> y IN v in
   let continuous_real =
      \(carrier:A->bool)
       (opens:(A->bool)->bool) (h:A->real).
        !v:real->bool.
          real_open v
          ==> opens {x:A | x IN carrier /\ h x IN v} in
   let bounded_continuous_nonnegative =
      \(carrier:A->bool)
       (opens:(A->bool)->bool) (h:A->real).
        continuous_real carrier opens h /\
        (!x:A. x IN carrier ==> &0 <= h x) /\
        ?bound:real. !x:A. x IN carrier ==> h x <= bound in
   let simple_nonnegative =
      \(carrier:A->bool)
       (events:(A->bool)->bool) (s:A->real).
        (!x:A. x IN carrier ==> &0 <= s x) /\
        FINITE (IMAGE s carrier) /\
        (!c:real. events {x:A | x IN carrier /\ s x = c}) in
   let simple_integral =
      \(carrier:A->bool)
       (mu:(A->bool)->real) (s:A->real).
        sum (IMAGE s carrier)
          (\c:real. c * mu {x:A | x IN carrier /\ s x = c}) in
   let lintegral_upper =
      \(carrier:A->bool)
       (events:(A->bool)->bool)
       (mu:(A->bool)->real) (h:A->real) (upper:real).
        !s:A->real.
          simple_nonnegative carrier events s /\
          (!x:A. x IN carrier ==> s x <= h x)
          ==> simple_integral carrier mu s <= upper in
   let has_lintegral =
      \(carrier:A->bool)
       (events:(A->bool)->bool)
       (mu:(A->bool)->real) (h:A->real) (z:real).
        &0 <= z /\
        lintegral_upper carrier events mu h z /\
        (!upper:real.
           &0 <= upper /\
           lintegral_upper carrier events mu h upper
           ==> z <= upper) in
   let lintegral =
      \(carrier:A->bool)
       (events:(A->bool)->bool)
       (mu:(A->bool)->real) (h:A->real).
        @z:real. has_lintegral carrier events mu h z in
   let measure_topology =
      \(carrier:A->bool)
       (events:(A->bool)->bool)
       (measure_opens:(((A->bool)->real)->bool)->bool).
        measure_opens {} /\
        measure_opens
          {mu:(A->bool)->real |
             finite_measure carrier events mu} /\
        (!u:((A->bool)->real)->bool.
           measure_opens u
           ==> u SUBSET
               {mu:(A->bool)->real |
                  finite_measure carrier events mu}) /\
        (!collection:(((A->bool)->real)->bool)->bool.
           (!u:((A->bool)->real)->bool.
              u IN collection ==> measure_opens u)
           ==> measure_opens (UNIONS collection)) /\
        (!u v:((A->bool)->real)->bool.
           measure_opens u /\ measure_opens v
           ==> measure_opens (u INTER v)) in
   let contains_weak_subbasis =
      \(carrier:A->bool)
       (opens:(A->bool)->bool)
       (events:(A->bool)->bool)
       (measure_opens:(((A->bool)->real)->bool)->bool).
        !h:A->real. !v:real->bool.
          bounded_continuous_nonnegative carrier opens h /\
          real_open v
          ==> measure_opens
                {mu:(A->bool)->real |
                   finite_measure carrier events mu /\
                   lintegral carrier events mu h IN v} in
   let weak_open =
      \(carrier:A->bool)
       (opens:(A->bool)->bool)
       (events:(A->bool)->bool)
       (u:((A->bool)->real)->bool).
        !measure_opens:(((A->bool)->real)->bool)->bool.
          measure_topology carrier events measure_opens /\
          contains_weak_subbasis
            carrier opens events measure_opens
          ==> measure_opens u in
   let compact_measure_set =
      \(carrier:A->bool)
       (opens:(A->bool)->bool)
       (events:(A->bool)->bool)
       (s:((A->bool)->real)->bool).
        s SUBSET
          {mu:(A->bool)->real |
             finite_measure carrier events mu} /\
        !cover:(((A->bool)->real)->bool)->bool.
          (!u:((A->bool)->real)->bool.
             u IN cover ==> weak_open carrier opens events u) /\
          s SUBSET UNIONS cover
          ==> ?subcover:(((A->bool)->real)->bool)->bool.
                subcover SUBSET cover /\
                FINITE subcover /\
                s SUBSET UNIONS subcover in
   !carrier:A->bool
    opens:(A->bool)->bool
    events:(A->bool)->bool
    u:num->real
    K:num->A->bool
    C:real.
      topology carrier opens /\
      hausdorff_space carrier opens /\
      borel_space carrier opens events /\
      &0 <= C /\
      (!n:num. &0 <= u n) /\
      sequence_tends u (&0) /\
      (!n:num. compact_set carrier opens (K n)) /\
      (normal_space carrier opens \/
       (!m n:num. m <= n ==> K m SUBSET K n))
      ==>
      compact_measure_set carrier opens events
        {mu:(A->bool)->real |
           finite_measure carrier events mu /\
           mu carrier <= C /\
           !n:num. mu (carrier DIFF K n) <= u n}`;;
