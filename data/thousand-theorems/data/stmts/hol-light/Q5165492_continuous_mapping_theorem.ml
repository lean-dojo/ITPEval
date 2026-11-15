(*
  Statement-only formalization of Thousand Theorems corpus artifact Q5165492,
  "Continuous mapping theorem": continuous composition preserves convergence
  in distribution for random variables on varying probability spaces along
  an arbitrary filter. This file contains no proof.
*)

let Q5165492_CONTINUOUS_MAPPING_THEOREM =
 `let real_tends =
      \(filter:(I->bool)->bool) (u:I->real) (z:real).
        !epsilon:real.
          &0 < epsilon
          ==> filter {i:I | abs(u i - z) < epsilon} in
   let sequence_tends =
      \(u:num->real) (z:real).
        !epsilon:real.
          &0 < epsilon
          ==> ?N:num.
                !n:num. N <= n ==> abs(u n - z) < epsilon in
   let is_filter =
      \(filter:(I->bool)->bool).
        filter (:I) /\
        (!s t:I->bool.
           filter s /\ s SUBSET t ==> filter t) /\
        (!s t:I->bool.
           filter s /\ filter t ==> filter (s INTER t)) in
   let topologyE =
      \(opens:(E->bool)->bool).
        opens {} /\
        opens (:E) /\
        (!collection:(E->bool)->bool.
           (!u:E->bool. u IN collection ==> opens u)
           ==> opens (UNIONS collection)) /\
        (!u v:E->bool.
           opens u /\ opens v ==> opens (u INTER v)) in
   let topologyF =
      \(opens:(F->bool)->bool).
        opens {} /\
        opens (:F) /\
        (!collection:(F->bool)->bool.
           (!u:F->bool. u IN collection ==> opens u)
           ==> opens (UNIONS collection)) /\
        (!u v:F->bool.
           opens u /\ opens v ==> opens (u INTER v)) in
   let sigmaE =
      \(events:(E->bool)->bool).
        events {} /\
        events (:E) /\
        (!s:E->bool.
           events s ==> events ((:E) DIFF s)) /\
        (!sets:num->E->bool.
           (!n. events (sets n))
           ==> events {x:E | ?n. x IN sets n}) in
   let sigmaF =
      \(events:(F->bool)->bool).
        events {} /\
        events (:F) /\
        (!s:F->bool.
           events s ==> events ((:F) DIFF s)) /\
        (!sets:num->F->bool.
           (!n. events (sets n))
           ==> events {x:F | ?n. x IN sets n}) in
   let sigmaB =
      \(carrier:B->bool) (events:(B->bool)->bool).
        events {} /\
        events carrier /\
        (!s:B->bool. events s ==> s SUBSET carrier) /\
        (!s:B->bool.
           events s ==> events (carrier DIFF s)) /\
        (!sets:num->B->bool.
           (!n. events (sets n))
           ==> events {x:B | ?n. x IN sets n}) in
   let sigmaC =
      \(carrier:C->bool) (events:(C->bool)->bool).
        events {} /\
        events carrier /\
        (!s:C->bool. events s ==> s SUBSET carrier) /\
        (!s:C->bool.
           events s ==> events (carrier DIFF s)) /\
        (!sets:num->C->bool.
           (!n. events (sets n))
           ==> events {x:C | ?n. x IN sets n}) in
   let borelF =
      \(opens:(F->bool)->bool) (s:F->bool).
        !events:(F->bool)->bool.
          sigmaF events /\
          (!u:F->bool. opens u ==> events u)
          ==> events s in
   let borel_spaceF =
      \(opens:(F->bool)->bool) (events:(F->bool)->bool).
        !s:F->bool. events s <=> borelF opens s in
   let opens_measurableE =
      \(opens:(E->bool)->bool) (events:(E->bool)->bool).
        !u:E->bool. opens u ==> events u in
   let real_open =
      \(u:real->bool).
        !x:real.
          x IN u
          ==> ?epsilon:real.
                &0 < epsilon /\
                !y:real. abs(y - x) < epsilon ==> y IN u in
   let continuous_realE =
      \(opens:(E->bool)->bool) (h:E->real).
        !u:real->bool.
          real_open u ==> opens {x:E | h x IN u} in
   let continuous_realF =
      \(opens:(F->bool)->bool) (h:F->real).
        !u:real->bool.
          real_open u ==> opens {x:F | h x IN u} in
   let bounded_continuousE =
      \(opens:(E->bool)->bool) (h:E->real).
        continuous_realE opens h /\
        ?bound:real. !x:E. abs(h x) <= bound in
   let bounded_continuousF =
      \(opens:(F->bool)->bool) (h:F->real).
        continuous_realF opens h /\
        ?bound:real. !x:F. abs(h x) <= bound in
   let continuousEF =
      \(opensE:(E->bool)->bool)
       (opensF:(F->bool)->bool) (g:E->F).
        !u:F->bool.
          opensF u ==> opensE {x:E | g x IN u} in
   let probabilityB =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->real).
        sigmaB carrier events /\
        mu {} = &0 /\
        mu carrier = &1 /\
        (!s:B->bool. events s ==> &0 <= mu s) /\
        (!sets:num->B->bool.
           (!n. events (sets n)) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> sequence_tends
                 (\N. sum {k:num | k < N} (\k. mu (sets k)))
                 (mu {x:B | ?k. x IN sets k})) in
   let probabilityC =
      \(carrier:C->bool) (events:(C->bool)->bool)
       (mu:(C->bool)->real).
        sigmaC carrier events /\
        mu {} = &0 /\
        mu carrier = &1 /\
        (!s:C->bool. events s ==> &0 <= mu s) /\
        (!sets:num->C->bool.
           (!n. events (sets n)) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> sequence_tends
                 (\N. sum {k:num | k < N} (\k. mu (sets k)))
                 (mu {x:C | ?k. x IN sets k})) in
   let probabilityE =
      \(events:(E->bool)->bool) (mu:(E->bool)->real).
        sigmaE events /\
        mu {} = &0 /\
        mu (:E) = &1 /\
        (!s:E->bool. events s ==> &0 <= mu s) /\
        (!sets:num->E->bool.
           (!n. events (sets n)) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> sequence_tends
                 (\N. sum {k:num | k < N} (\k. mu (sets k)))
                 (mu {x:E | ?k. x IN sets k})) in
   let probabilityF =
      \(events:(F->bool)->bool) (mu:(F->bool)->real).
        sigmaF events /\
        mu {} = &0 /\
        mu (:F) = &1 /\
        (!s:F->bool. events s ==> &0 <= mu s) /\
        (!sets:num->F->bool.
           (!n. events (sets n)) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> sequence_tends
                 (\N. sum {k:num | k < N} (\k. mu (sets k)))
                 (mu {x:F | ?k. x IN sets k})) in
   let measurableBE =
      \(carrier:B->bool) (eventsB:(B->bool)->bool)
       (eventsE:(E->bool)->bool) (f:B->E).
        !s:E->bool.
          eventsE s
          ==> eventsB {x:B | x IN carrier /\ f x IN s} in
   let measurableBF =
      \(carrier:B->bool) (eventsB:(B->bool)->bool)
       (eventsF:(F->bool)->bool) (f:B->F).
        !s:F->bool.
          eventsF s
          ==> eventsB {x:B | x IN carrier /\ f x IN s} in
   let measurableCE =
      \(carrier:C->bool) (eventsC:(C->bool)->bool)
       (eventsE:(E->bool)->bool) (f:C->E).
        !s:E->bool.
          eventsE s
          ==> eventsC {x:C | x IN carrier /\ f x IN s} in
   let measurableCF =
      \(carrier:C->bool) (eventsC:(C->bool)->bool)
       (eventsF:(F->bool)->bool) (f:C->F).
        !s:F->bool.
          eventsF s
          ==> eventsC {x:C | x IN carrier /\ f x IN s} in
   let ae_equalBE =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->real) (f:B->E) (g:B->E).
        ?null:B->bool.
          events null /\
          mu null = &0 /\
          {x:B | x IN carrier /\ ~(f x = g x)} SUBSET null in
   let ae_equalBF =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->real) (f:B->F) (g:B->F).
        ?null:B->bool.
          events null /\
          mu null = &0 /\
          {x:B | x IN carrier /\ ~(f x = g x)} SUBSET null in
   let ae_equalCE =
      \(carrier:C->bool) (events:(C->bool)->bool)
       (mu:(C->bool)->real) (f:C->E) (g:C->E).
        ?null:C->bool.
          events null /\
          mu null = &0 /\
          {x:C | x IN carrier /\ ~(f x = g x)} SUBSET null in
   let ae_equalCF =
      \(carrier:C->bool) (events:(C->bool)->bool)
       (mu:(C->bool)->real) (f:C->F) (g:C->F).
        ?null:C->bool.
          events null /\
          mu null = &0 /\
          {x:C | x IN carrier /\ ~(f x = g x)} SUBSET null in
   let ae_measurableBE =
      \(carrier:B->bool) (eventsB:(B->bool)->bool)
       (mu:(B->bool)->real) (eventsE:(E->bool)->bool)
       (f:B->E).
        ?version:B->E.
          measurableBE carrier eventsB eventsE version /\
          ae_equalBE carrier eventsB mu f version in
   let ae_measurableBF =
      \(carrier:B->bool) (eventsB:(B->bool)->bool)
       (mu:(B->bool)->real) (eventsF:(F->bool)->bool)
       (f:B->F).
        ?version:B->F.
          measurableBF carrier eventsB eventsF version /\
          ae_equalBF carrier eventsB mu f version in
   let ae_measurableCE =
      \(carrier:C->bool) (eventsC:(C->bool)->bool)
       (mu:(C->bool)->real) (eventsE:(E->bool)->bool)
       (f:C->E).
        ?version:C->E.
          measurableCE carrier eventsC eventsE version /\
          ae_equalCE carrier eventsC mu f version in
   let ae_measurableCF =
      \(carrier:C->bool) (eventsC:(C->bool)->bool)
       (mu:(C->bool)->real) (eventsF:(F->bool)->bool)
       (f:C->F).
        ?version:C->F.
          measurableCF carrier eventsC eventsF version /\
          ae_equalCF carrier eventsC mu f version in
   let mapBE =
      \(carrier:B->bool) (eventsB:(B->bool)->bool)
       (mu:(B->bool)->real) (eventsE:(E->bool)->bool)
       (f:B->E) (law:(E->bool)->real).
        probabilityE eventsE law /\
        ?version:B->E.
          measurableBE carrier eventsB eventsE version /\
          ae_equalBE carrier eventsB mu f version /\
          (!s:E->bool.
             eventsE s
             ==> law s =
                 mu {x:B | x IN carrier /\ version x IN s}) in
   let mapBF =
      \(carrier:B->bool) (eventsB:(B->bool)->bool)
       (mu:(B->bool)->real) (eventsF:(F->bool)->bool)
       (f:B->F) (law:(F->bool)->real).
        probabilityF eventsF law /\
        ?version:B->F.
          measurableBF carrier eventsB eventsF version /\
          ae_equalBF carrier eventsB mu f version /\
          (!s:F->bool.
             eventsF s
             ==> law s =
                 mu {x:B | x IN carrier /\ version x IN s}) in
   let mapCE =
      \(carrier:C->bool) (eventsC:(C->bool)->bool)
       (mu:(C->bool)->real) (eventsE:(E->bool)->bool)
       (f:C->E) (law:(E->bool)->real).
        probabilityE eventsE law /\
        ?version:C->E.
          measurableCE carrier eventsC eventsE version /\
          ae_equalCE carrier eventsC mu f version /\
          (!s:E->bool.
             eventsE s
             ==> law s =
                 mu {x:C | x IN carrier /\ version x IN s}) in
   let mapCF =
      \(carrier:C->bool) (eventsC:(C->bool)->bool)
       (mu:(C->bool)->real) (eventsF:(F->bool)->bool)
       (f:C->F) (law:(F->bool)->real).
        probabilityF eventsF law /\
        ?version:C->F.
          measurableCF carrier eventsC eventsF version /\
          ae_equalCF carrier eventsC mu f version /\
          (!s:F->bool.
             eventsF s
             ==> law s =
                 mu {x:C | x IN carrier /\ version x IN s}) in
   let simpleE =
      \(events:(E->bool)->bool) (s:E->real).
        (!x:E. &0 <= s x) /\
        FINITE (IMAGE s (:E)) /\
        (!c:real. events {x:E | s x = c}) in
   let simpleF =
      \(events:(F->bool)->bool) (s:F->real).
        (!x:F. &0 <= s x) /\
        FINITE (IMAGE s (:F)) /\
        (!c:real. events {x:F | s x = c}) in
   let simple_integralE =
      \(mu:(E->bool)->real) (s:E->real) (z:real).
        ?n:num enum:num->real partial:num->real.
          (!c:real.
             c IN IMAGE s (:E) <=>
             ?i:num. i < n /\ enum i = c) /\
          (!i j:num.
             i < n /\ j < n /\ enum i = enum j ==> i = j) /\
          partial 0 = &0 /\
          (!i:num.
             i < n
             ==> partial (SUC i) =
                 mu {x:E | s x = enum i} * enum i +
                 partial i) /\
          z = partial n in
   let simple_integralF =
      \(mu:(F->bool)->real) (s:F->real) (z:real).
        ?n:num enum:num->real partial:num->real.
          (!c:real.
             c IN IMAGE s (:F) <=>
             ?i:num. i < n /\ enum i = c) /\
          (!i j:num.
             i < n /\ j < n /\ enum i = enum j ==> i = j) /\
          partial 0 = &0 /\
          (!i:num.
             i < n
             ==> partial (SUC i) =
                 mu {x:F | s x = enum i} * enum i +
                 partial i) /\
          z = partial n in
   let lintegral_upperE =
      \(events:(E->bool)->bool) (mu:(E->bool)->real)
       (h:E->real) (upper:real).
        !s:E->real z:real.
          simpleE events s /\
          (!x:E. s x <= h x) /\
          simple_integralE mu s z
          ==> z <= upper in
   let lintegral_upperF =
      \(events:(F->bool)->bool) (mu:(F->bool)->real)
       (h:F->real) (upper:real).
        !s:F->real z:real.
          simpleF events s /\
          (!x:F. s x <= h x) /\
          simple_integralF mu s z
          ==> z <= upper in
   let has_lintegralE =
      \(events:(E->bool)->bool) (mu:(E->bool)->real)
       (h:E->real) (z:real).
        &0 <= z /\
        lintegral_upperE events mu h z /\
        (!upper:real.
           &0 <= upper /\
           lintegral_upperE events mu h upper
           ==> z <= upper) in
   let has_lintegralF =
      \(events:(F->bool)->bool) (mu:(F->bool)->real)
       (h:F->real) (z:real).
        &0 <= z /\
        lintegral_upperF events mu h z /\
        (!upper:real.
           &0 <= upper /\
           lintegral_upperF events mu h upper
           ==> z <= upper) in
   let lintegralE =
      \(events:(E->bool)->bool) (mu:(E->bool)->real)
       (h:E->real).
        @z:real. has_lintegralE events mu h z in
   let lintegralF =
      \(events:(F->bool)->bool) (mu:(F->bool)->real)
       (h:F->real).
        @z:real. has_lintegralF events mu h z in
   let integralE =
      \(events:(E->bool)->bool) (mu:(E->bool)->real)
       (h:E->real).
        lintegralE events mu
          (\x:E. if &0 <= h x then h x else &0) -
        lintegralE events mu
          (\x:E. if &0 <= --(h x) then --(h x) else &0) in
   let integralF =
      \(events:(F->bool)->bool) (mu:(F->bool)->real)
       (h:F->real).
        lintegralF events mu
          (\x:F. if &0 <= h x then h x else &0) -
        lintegralF events mu
          (\x:F. if &0 <= --(h x) then --(h x) else &0) in
   let weak_tendsE =
      \(opens:(E->bool)->bool) (events:(E->bool)->bool)
       (filter:(I->bool)->bool)
       (laws:I->(E->bool)->real) (limit:(E->bool)->real).
        !h:E->real.
          bounded_continuousE opens h
          ==> real_tends filter
                (\i:I. integralE events (laws i) h)
                (integralE events limit h) in
   let weak_tendsF =
      \(opens:(F->bool)->bool) (events:(F->bool)->bool)
       (filter:(I->bool)->bool)
       (laws:I->(F->bool)->real) (limit:(F->bool)->real).
        !h:F->real.
          bounded_continuousF opens h
          ==> real_tends filter
                (\i:I. integralF events (laws i) h)
                (integralF events limit h) in
   let tends_in_distributionE =
      \(carrier:I->B->bool)
       (events:I->(B->bool)->bool)
       (mu:I->(B->bool)->real)
       (limit_carrier:C->bool)
       (limit_events:(C->bool)->bool)
       (limit_mu:(C->bool)->real)
       (target_events:(E->bool)->bool)
       (target_opens:(E->bool)->bool)
       (X:I->B->E) (filter:(I->bool)->bool) (Z:C->E).
        (!i:I.
           ae_measurableBE
             (carrier i) (events i) (mu i)
             target_events (X i)) /\
        ae_measurableCE
          limit_carrier limit_events limit_mu target_events Z /\
        ?laws:I->(E->bool)->real limit_law:(E->bool)->real.
          (!i:I.
             mapBE
               (carrier i) (events i) (mu i)
               target_events (X i) (laws i)) /\
          mapCE
            limit_carrier limit_events limit_mu
            target_events Z limit_law /\
          weak_tendsE
            target_opens target_events filter laws limit_law in
   let tends_in_distributionF =
      \(carrier:I->B->bool)
       (events:I->(B->bool)->bool)
       (mu:I->(B->bool)->real)
       (limit_carrier:C->bool)
       (limit_events:(C->bool)->bool)
       (limit_mu:(C->bool)->real)
       (target_events:(F->bool)->bool)
       (target_opens:(F->bool)->bool)
       (X:I->B->F) (filter:(I->bool)->bool) (Z:C->F).
        (!i:I.
           ae_measurableBF
             (carrier i) (events i) (mu i)
             target_events (X i)) /\
        ae_measurableCF
          limit_carrier limit_events limit_mu target_events Z /\
        ?laws:I->(F->bool)->real limit_law:(F->bool)->real.
          (!i:I.
             mapBF
               (carrier i) (events i) (mu i)
               target_events (X i) (laws i)) /\
          mapCF
            limit_carrier limit_events limit_mu
            target_events Z limit_law /\
          weak_tendsF
            target_opens target_events filter laws limit_law in
   !carrier:I->B->bool
    events:I->(B->bool)->bool
    mu:I->(B->bool)->real
    limit_carrier:C->bool
    limit_events:(C->bool)->bool
    limit_mu:(C->bool)->real
    opensE:(E->bool)->bool
    target_eventsE:(E->bool)->bool
    opensF:(F->bool)->bool
    target_eventsF:(F->bool)->bool
    X:I->B->E
    Z:C->E
    filter:(I->bool)->bool
    g:E->F.
      (!i:I.
         probabilityB (carrier i) (events i) (mu i)) /\
      probabilityC limit_carrier limit_events limit_mu /\
      topologyE opensE /\
      sigmaE target_eventsE /\
      opens_measurableE opensE target_eventsE /\
      topologyF opensF /\
      sigmaF target_eventsF /\
      borel_spaceF opensF target_eventsF /\
      is_filter filter /\
      continuousEF opensE opensF g /\
      tends_in_distributionE
        carrier events mu
        limit_carrier limit_events limit_mu
        target_eventsE opensE X filter Z
      ==>
      tends_in_distributionF
        carrier events mu
        limit_carrier limit_events limit_mu
        target_eventsF opensF
        (\i:I x:B. g (X i x)) filter
        (\x:C. g (Z x))`;;
