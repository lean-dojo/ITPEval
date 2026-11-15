(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1149022,
  "Fubini's theorem": the Bochner integral of an integrable function over the
  product of two s-finite measure spaces equals its iterated Bochner integral.
  This file contains no proof.
*)

let Q1149022_FUBINI_S_THEOREM =
 `let enonnegative =
      \(z:bool#real).
        (FST z /\ SND z = &0) \/
        (~(FST z) /\ &0 <= SND z) in
   let ezero = (F,&0) in
   let etop = (T,&0) in
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
   let ele =
      \(x:bool#real) (y:bool#real).
        FST y \/ (~(FST x) /\ SND x <= SND y) in
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
   let product_carrier =
      \(carrierB:B->bool) (carrierC:C->bool).
        {p:B#C | FST p IN carrierB /\ SND p IN carrierC} in
   let sigmaB =
      \(carrier:B->bool) (events:(B->bool)->bool).
        events {} /\
        events carrier /\
        (!s:B->bool. events s ==> s SUBSET carrier) /\
        (!s:B->bool. events s ==> events (carrier DIFF s)) /\
        (!sets:num->B->bool.
           (!n. events (sets n))
           ==> events {x:B | ?n. x IN sets n}) in
   let sigmaC =
      \(carrier:C->bool) (events:(C->bool)->bool).
        events {} /\
        events carrier /\
        (!s:C->bool. events s ==> s SUBSET carrier) /\
        (!s:C->bool. events s ==> events (carrier DIFF s)) /\
        (!sets:num->C->bool.
           (!n. events (sets n))
           ==> events {x:C | ?n. x IN sets n}) in
   let sigmaBC =
      \(carrier:(B#C)->bool)
       (events:((B#C)->bool)->bool).
        events {} /\
        events carrier /\
        (!s:(B#C)->bool.
           events s ==> s SUBSET carrier) /\
        (!s:(B#C)->bool.
           events s ==> events (carrier DIFF s)) /\
        (!sets:num->(B#C)->bool.
           (!n. events (sets n))
           ==> events {x:B#C | ?n. x IN sets n}) in
   let measureB =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real).
        sigmaB carrier events /\
        (!s:B->bool. enonnegative (mu s)) /\
        mu {} = ezero /\
        (!sets:num->B->bool.
           (!n. events (sets n)) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> esum (\n. mu (sets n))
                     (mu {x:B | ?n. x IN sets n})) in
   let measureC =
      \(carrier:C->bool) (events:(C->bool)->bool)
       (mu:(C->bool)->bool#real).
        sigmaC carrier events /\
        (!s:C->bool. enonnegative (mu s)) /\
        mu {} = ezero /\
        (!sets:num->C->bool.
           (!n. events (sets n)) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> esum (\n. mu (sets n))
                     (mu {x:C | ?n. x IN sets n})) in
   let measureBC =
      \(carrier:(B#C)->bool)
       (events:((B#C)->bool)->bool)
       (mu:((B#C)->bool)->bool#real).
        sigmaBC carrier events /\
        (!s:(B#C)->bool. enonnegative (mu s)) /\
        mu {} = ezero /\
        (!sets:num->(B#C)->bool.
           (!n. events (sets n)) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> esum (\n. mu (sets n))
                     (mu {x:B#C | ?n. x IN sets n})) in
   let finite_measureB =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real).
        measureB carrier events mu /\ ~(FST (mu carrier)) in
   let finite_measureC =
      \(carrier:C->bool) (events:(C->bool)->bool)
       (mu:(C->bool)->bool#real).
        measureC carrier events mu /\ ~(FST (mu carrier)) in
   let sfiniteB =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real).
        measureB carrier events mu /\
        ?parts:num->(B->bool)->bool#real.
          (!n. finite_measureB carrier events (parts n)) /\
          (!s:B->bool.
             events s
             ==> esum (\n. parts n s) (mu s)) in
   let sfiniteC =
      \(carrier:C->bool) (events:(C->bool)->bool)
       (mu:(C->bool)->bool#real).
        measureC carrier events mu /\
        ?parts:num->(C->bool)->bool#real.
          (!n. finite_measureC carrier events (parts n)) /\
          (!s:C->bool.
             events s
             ==> esum (\n. parts n s) (mu s)) in
   let product_events =
      \(carrierB:B->bool) (carrierC:C->bool)
       (eventsB:(B->bool)->bool)
       (eventsC:(C->bool)->bool)
       (s:(B#C)->bool).
        !events:((B#C)->bool)->bool.
          sigmaBC (product_carrier carrierB carrierC) events /\
          (!u:B->bool. !v:C->bool.
             eventsB u /\ eventsC v
             ==> events {p:B#C |
                           FST p IN u /\ SND p IN v})
          ==> events s in
   let almost_everywhereB =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real)
       (P:B->bool).
        ?N:B->bool.
          events N /\
          mu N = ezero /\
          {x:B | x IN carrier /\ ~(P x)} SUBSET N in
   let almost_everywhereC =
      \(carrier:C->bool) (events:(C->bool)->bool)
       (mu:(C->bool)->bool#real)
       (P:C->bool).
        ?N:C->bool.
          events N /\
          mu N = ezero /\
          {x:C | x IN carrier /\ ~(P x)} SUBSET N in
   let almost_everywhereBC =
      \(carrier:(B#C)->bool)
       (events:((B#C)->bool)->bool)
       (mu:((B#C)->bool)->bool#real)
       (P:(B#C)->bool).
        ?N:(B#C)->bool.
          events N /\
          mu N = ezero /\
          {x:B#C | x IN carrier /\ ~(P x)} SUBSET N in
   let normed_real_vector_space =
      \(zero:A) (add:A->A->A) (neg:A->A)
       (smul:real->A->A) (norm:A->real).
        (!x y:A. add x y = add y x) /\
        (!x y z:A. add (add x y) z = add x (add y z)) /\
        (!x:A. add x zero = x) /\
        (!x:A. add x (neg x) = zero) /\
        (!x:A. neg (neg x) = x) /\
        (!x:A. smul (&1) x = x) /\
        (!a b:real x:A. smul (a * b) x = smul a (smul b x)) /\
        (!a b:real x:A.
           smul (a + b) x = add (smul a x) (smul b x)) /\
        (!a:real x y:A.
           smul a (add x y) = add (smul a x) (smul a y)) /\
        (!x:A. smul (&0) x = zero) /\
        (!a:real. smul a zero = zero) /\
        (!x:A. &0 <= norm x) /\
        (!x:A. norm x = &0 <=> x = zero) /\
        (!a:real x:A. norm (smul a x) = abs a * norm x) /\
        (!x y:A. norm (add x y) <= norm x + norm y) in
   let scalar_tends =
      \(u:num->real) (l:real).
        !e. &0 < e ==> ?N. !n. N <= n ==> abs(u n - l) < e in
   let vector_tends =
      \(zero:A) (add:A->A->A) (neg:A->A) (norm:A->real)
       (u:num->A) (l:A).
        !e. &0 < e
            ==> ?N. !n. N <= n
                       ==> norm (add (u n) (neg l)) < e in
   let complete_space =
      \(zero:A) (add:A->A->A) (neg:A->A) (norm:A->real).
        !u:num->A.
          (!e. &0 < e
               ==> ?N. !m n.
                     N <= m /\ N <= n
                     ==> norm (add (u m) (neg (u n))) < e)
          ==> ?l:A. vector_tends zero add neg norm u l in
   let simple_scalarB =
      \(carrier:B->bool) (events:(B->bool)->bool) (s:B->real).
        (!x:B. x IN carrier ==> &0 <= s x) /\
        FINITE (IMAGE s carrier) /\
        (!c:real. events {x:B | x IN carrier /\ s x = c}) in
   let simple_scalarC =
      \(carrier:C->bool) (events:(C->bool)->bool) (s:C->real).
        (!x:C. x IN carrier ==> &0 <= s x) /\
        FINITE (IMAGE s carrier) /\
        (!c:real. events {x:C | x IN carrier /\ s x = c}) in
   let simple_scalarBC =
      \(carrier:(B#C)->bool)
       (events:((B#C)->bool)->bool) (s:(B#C)->real).
        (!x:B#C. x IN carrier ==> &0 <= s x) /\
        FINITE (IMAGE s carrier) /\
        (!c:real. events {x:B#C | x IN carrier /\ s x = c}) in
   let simple_vectorB =
      \(carrier:B->bool) (events:(B->bool)->bool) (s:B->A).
        FINITE (IMAGE s carrier) /\
        (!c:A. events {x:B | x IN carrier /\ s x = c}) in
   let simple_vectorC =
      \(carrier:C->bool) (events:(C->bool)->bool) (s:C->A).
        FINITE (IMAGE s carrier) /\
        (!c:A. events {x:C | x IN carrier /\ s x = c}) in
   let simple_vectorBC =
      \(carrier:(B#C)->bool)
       (events:((B#C)->bool)->bool) (s:(B#C)->A).
        FINITE (IMAGE s carrier) /\
        (!c:A. events {x:B#C | x IN carrier /\ s x = c}) in
   let strongly_measurableB =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (zero:A) (add:A->A->A) (neg:A->A) (norm:A->real)
       (h:B->A).
        ?s:num->B->A.
          (!n. simple_vectorB carrier events (s n)) /\
          (!x:B.
             x IN carrier
             ==> vector_tends zero add neg norm
               (\n. s n x) (h x)) in
   let strongly_measurableC =
      \(carrier:C->bool) (events:(C->bool)->bool)
       (zero:A) (add:A->A->A) (neg:A->A) (norm:A->real)
       (h:C->A).
        ?s:num->C->A.
          (!n. simple_vectorC carrier events (s n)) /\
          (!x:C.
             x IN carrier
             ==> vector_tends zero add neg norm
               (\n. s n x) (h x)) in
   let strongly_measurableBC =
      \(carrier:(B#C)->bool)
       (events:((B#C)->bool)->bool)
       (zero:A) (add:A->A->A) (neg:A->A) (norm:A->real)
       (h:(B#C)->A).
        ?s:num->(B#C)->A.
          (!n. simple_vectorBC carrier events (s n)) /\
          (!x:B#C.
             x IN carrier
             ==> vector_tends zero add neg norm
               (\n. s n x) (h x)) in
   let ae_strongly_measurableB =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real)
       (zero:A) (add:A->A->A) (neg:A->A) (norm:A->real)
       (h:B->A).
        ?g:B->A.
          strongly_measurableB carrier events zero add neg norm g /\
          almost_everywhereB carrier events mu
            (\x:B. h x = g x) in
   let ae_strongly_measurableC =
      \(carrier:C->bool) (events:(C->bool)->bool)
       (mu:(C->bool)->bool#real)
       (zero:A) (add:A->A->A) (neg:A->A) (norm:A->real)
       (h:C->A).
        ?g:C->A.
          strongly_measurableC carrier events zero add neg norm g /\
          almost_everywhereC carrier events mu
            (\x:C. h x = g x) in
   let ae_strongly_measurableBC =
      \(carrier:(B#C)->bool)
       (events:((B#C)->bool)->bool)
       (mu:((B#C)->bool)->bool#real)
       (zero:A) (add:A->A->A) (neg:A->A) (norm:A->real)
       (h:(B#C)->A).
        ?g:(B#C)->A.
          strongly_measurableBC
            carrier events zero add neg norm g /\
          almost_everywhereBC carrier events mu
            (\x:B#C. h x = g x) in
   let integrable_simple_scalarB =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real) (s:B->real).
        simple_scalarB carrier events s /\
        (!c:real.
           c IN IMAGE s carrier /\ ~(c = &0)
           ==> ~(FST (mu {x:B |
                            x IN carrier /\ s x = c}))) in
   let integrable_simple_scalarC =
      \(carrier:C->bool) (events:(C->bool)->bool)
       (mu:(C->bool)->bool#real) (s:C->real).
        simple_scalarC carrier events s /\
        (!c:real.
           c IN IMAGE s carrier /\ ~(c = &0)
           ==> ~(FST (mu {x:C |
                            x IN carrier /\ s x = c}))) in
   let integrable_simple_scalarBC =
      \(carrier:(B#C)->bool)
       (events:((B#C)->bool)->bool)
       (mu:((B#C)->bool)->bool#real) (s:(B#C)->real).
        simple_scalarBC carrier events s /\
        (!c:real.
           c IN IMAGE s carrier /\ ~(c = &0)
           ==> ~(FST (mu {x:B#C |
                            x IN carrier /\ s x = c}))) in
   let integrable_simple_vectorB =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real) (zero:A) (s:B->A).
        simple_vectorB carrier events s /\
        (!c:A.
           c IN IMAGE s carrier /\ ~(c = zero)
           ==> ~(FST (mu {x:B |
                            x IN carrier /\ s x = c}))) in
   let integrable_simple_vectorC =
      \(carrier:C->bool) (events:(C->bool)->bool)
       (mu:(C->bool)->bool#real) (zero:A) (s:C->A).
        simple_vectorC carrier events s /\
        (!c:A.
           c IN IMAGE s carrier /\ ~(c = zero)
           ==> ~(FST (mu {x:C |
                            x IN carrier /\ s x = c}))) in
   let integrable_simple_vectorBC =
      \(carrier:(B#C)->bool)
       (events:((B#C)->bool)->bool)
       (mu:((B#C)->bool)->bool#real) (zero:A) (s:(B#C)->A).
        simple_vectorBC carrier events s /\
        (!c:A.
           c IN IMAGE s carrier /\ ~(c = zero)
           ==> ~(FST (mu {x:B#C |
                            x IN carrier /\ s x = c}))) in
   let simple_scalar_integralB =
      \(carrier:B->bool) (mu:(B->bool)->bool#real)
       (s:B->real) (z:real).
        ?n enum partial.
          (!c:real.
             c IN IMAGE s carrier <=>
             ?i. i < n /\ enum i = c) /\
          (!i j. i < n /\ j < n /\ enum i = enum j ==> i = j) /\
          partial 0 = &0 /\
          (!i. i < n
               ==> partial (SUC i) =
                   SND (mu {x:B |
                              x IN carrier /\ s x = enum i}) *
                   enum i +
                   partial i) /\
          z = partial n in
   let simple_scalar_integralC =
      \(carrier:C->bool) (mu:(C->bool)->bool#real)
       (s:C->real) (z:real).
        ?n enum partial.
          (!c:real.
             c IN IMAGE s carrier <=>
             ?i. i < n /\ enum i = c) /\
          (!i j. i < n /\ j < n /\ enum i = enum j ==> i = j) /\
          partial 0 = &0 /\
          (!i. i < n
               ==> partial (SUC i) =
                   SND (mu {x:C |
                              x IN carrier /\ s x = enum i}) *
                   enum i +
                   partial i) /\
          z = partial n in
   let simple_scalar_integralBC =
      \(carrier:(B#C)->bool)
       (mu:((B#C)->bool)->bool#real)
       (s:(B#C)->real) (z:real).
        ?n enum partial.
          (!c:real.
             c IN IMAGE s carrier <=>
             ?i. i < n /\ enum i = c) /\
          (!i j. i < n /\ j < n /\ enum i = enum j ==> i = j) /\
          partial 0 = &0 /\
          (!i. i < n
               ==> partial (SUC i) =
                   SND (mu {x:B#C |
                              x IN carrier /\ s x = enum i}) *
                   enum i +
                   partial i) /\
          z = partial n in
   let simple_vector_integralB =
      \(carrier:B->bool) (mu:(B->bool)->bool#real)
       (zero:A) (add:A->A->A) (smul:real->A->A)
       (s:B->A) (z:A).
        ?n enum partial.
          (!c:A.
             c IN IMAGE s carrier <=>
             ?i. i < n /\ enum i = c) /\
          (!i j. i < n /\ j < n /\ enum i = enum j ==> i = j) /\
          partial 0 = zero /\
          (!i. i < n
               ==> partial (SUC i) =
                   add
                     (smul
                       (SND (mu {x:B |
                                  x IN carrier /\ s x = enum i}))
                       (enum i))
                     (partial i)) /\
          z = partial n in
   let simple_vector_integralC =
      \(carrier:C->bool) (mu:(C->bool)->bool#real)
       (zero:A) (add:A->A->A) (smul:real->A->A)
       (s:C->A) (z:A).
        ?n enum partial.
          (!c:A.
             c IN IMAGE s carrier <=>
             ?i. i < n /\ enum i = c) /\
          (!i j. i < n /\ j < n /\ enum i = enum j ==> i = j) /\
          partial 0 = zero /\
          (!i. i < n
               ==> partial (SUC i) =
                   add
                     (smul
                       (SND (mu {x:C |
                                  x IN carrier /\ s x = enum i}))
                       (enum i))
                     (partial i)) /\
          z = partial n in
   let simple_vector_integralBC =
      \(carrier:(B#C)->bool)
       (mu:((B#C)->bool)->bool#real)
       (zero:A) (add:A->A->A) (smul:real->A->A)
       (s:(B#C)->A) (z:A).
        ?n enum partial.
          (!c:A.
             c IN IMAGE s carrier <=>
             ?i. i < n /\ enum i = c) /\
          (!i j. i < n /\ j < n /\ enum i = enum j ==> i = j) /\
          partial 0 = zero /\
          (!i. i < n
               ==> partial (SUC i) =
                   add
                     (smul
                       (SND (mu {x:B#C |
                                  x IN carrier /\ s x = enum i}))
                       (enum i))
                     (partial i)) /\
          z = partial n in
   let simple_lintegralB =
      \(carrier:B->bool) (mu:(B->bool)->bool#real)
       (s:B->real) (z:bool#real).
        ?n enum partial.
          (!c:real.
             c IN IMAGE s carrier <=>
             ?i. i < n /\ enum i = c) /\
          (!i j. i < n /\ j < n /\ enum i = enum j ==> i = j) /\
          partial 0 = ezero /\
          (!i. i < n
               ==> partial (SUC i) =
                   eadd
                     (partial i)
                     (emul
                       (F,enum i)
                       (mu {x:B |
                              x IN carrier /\ s x = enum i}))) /\
          z = partial n in
   let has_lintegralB =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real)
       (h:B->bool#real) (r:bool#real).
        enonnegative r /\
        (!s:B->real z:bool#real.
           simple_scalarB carrier events s /\
           (!x:B. x IN carrier ==> ele (F,s x) (h x)) /\
           simple_lintegralB carrier mu s z
           ==> ele z r) /\
        (!u:bool#real.
           enonnegative u /\
           (!s:B->real z:bool#real.
              simple_scalarB carrier events s /\
              (!x:B. x IN carrier ==> ele (F,s x) (h x)) /\
              simple_lintegralB carrier mu s z
              ==> ele z u)
           ==> ele r u) in
   let is_product_measure =
      \(carrierB:B->bool) (carrierC:C->bool)
       (eventsB:(B->bool)->bool)
       (eventsC:(C->bool)->bool)
       (mu:(B->bool)->bool#real)
       (nu:(C->bool)->bool#real)
       (rho:((B#C)->bool)->bool#real).
        measureBC
          (product_carrier carrierB carrierC)
          (product_events carrierB carrierC eventsB eventsC)
          rho /\
        (!s:(B#C)->bool.
           product_events carrierB carrierC eventsB eventsC s
           ==> has_lintegralB
                 carrierB eventsB mu
                 (\x:B.
                    nu {y:C |
                          y IN carrierC /\ (x,y) IN s})
                 (rho s)) in
   let product_measure =
      \(carrierB:B->bool) (carrierC:C->bool)
       (eventsB:(B->bool)->bool)
       (eventsC:(C->bool)->bool)
       (mu:(B->bool)->bool#real)
       (nu:(C->bool)->bool#real).
        @rho:((B#C)->bool)->bool#real.
          is_product_measure
            carrierB carrierC eventsB eventsC mu nu rho in
   let nonnegative_upperB =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real) (h:B->real) (u:real).
        !s:B->real z:real.
          integrable_simple_scalarB carrier events mu s /\
          (!x:B. x IN carrier ==> s x <= h x) /\
          simple_scalar_integralB carrier mu s z
          ==> z <= u in
   let nonnegative_upperC =
      \(carrier:C->bool) (events:(C->bool)->bool)
       (mu:(C->bool)->bool#real) (h:C->real) (u:real).
        !s:C->real z:real.
          integrable_simple_scalarC carrier events mu s /\
          (!x:C. x IN carrier ==> s x <= h x) /\
          simple_scalar_integralC carrier mu s z
          ==> z <= u in
   let nonnegative_upperBC =
      \(carrier:(B#C)->bool)
       (events:((B#C)->bool)->bool)
       (mu:((B#C)->bool)->bool#real)
       (h:(B#C)->real) (u:real).
        !s:(B#C)->real z:real.
          integrable_simple_scalarBC carrier events mu s /\
          (!x:B#C. x IN carrier ==> s x <= h x) /\
          simple_scalar_integralBC carrier mu s z
          ==> z <= u in
   let has_nonnegative_integralB =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real) (h:B->real) (r:real).
        &0 <= r /\
        nonnegative_upperB carrier events mu h r /\
        (!u:real.
           &0 <= u /\ nonnegative_upperB carrier events mu h u
           ==> r <= u) in
   let has_nonnegative_integralC =
      \(carrier:C->bool) (events:(C->bool)->bool)
       (mu:(C->bool)->bool#real) (h:C->real) (r:real).
        &0 <= r /\
        nonnegative_upperC carrier events mu h r /\
        (!u:real.
           &0 <= u /\ nonnegative_upperC carrier events mu h u
           ==> r <= u) in
   let has_nonnegative_integralBC =
      \(carrier:(B#C)->bool)
       (events:((B#C)->bool)->bool)
       (mu:((B#C)->bool)->bool#real)
       (h:(B#C)->real) (r:real).
        &0 <= r /\
        nonnegative_upperBC carrier events mu h r /\
        (!u:real.
           &0 <= u /\ nonnegative_upperBC carrier events mu h u
           ==> r <= u) in
   let vector_integrableB =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real)
       (zero:A) (add:A->A->A) (neg:A->A) (norm:A->real)
       (h:B->A).
        ae_strongly_measurableB
          carrier events mu zero add neg norm h /\
        (?r:real.
           has_nonnegative_integralB carrier events mu
             (\x:B. norm(h x)) r) in
   let vector_integrableC =
      \(carrier:C->bool) (events:(C->bool)->bool)
       (mu:(C->bool)->bool#real)
       (zero:A) (add:A->A->A) (neg:A->A) (norm:A->real)
       (h:C->A).
        ae_strongly_measurableC
          carrier events mu zero add neg norm h /\
        (?r:real.
           has_nonnegative_integralC carrier events mu
             (\x:C. norm(h x)) r) in
   let vector_integrableBC =
      \(carrier:(B#C)->bool)
       (events:((B#C)->bool)->bool)
       (mu:((B#C)->bool)->bool#real)
       (zero:A) (add:A->A->A) (neg:A->A) (norm:A->real)
       (h:(B#C)->A).
        ae_strongly_measurableBC
          carrier events mu zero add neg norm h /\
        (?r:real.
           has_nonnegative_integralBC carrier events mu
             (\x:B#C. norm(h x)) r) in
   let has_bochner_integralB =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real)
       (zero:A) (add:A->A->A) (neg:A->A)
       (smul:real->A->A) (norm:A->real)
       (h:B->A) (z:A).
        ?s:num->B->A ints:num->A.
          (!n. integrable_simple_vectorB
                 carrier events mu zero (s n)) /\
          (!n. simple_vector_integralB
                 carrier mu zero add smul (s n) (ints n)) /\
          (!e. &0 < e
               ==> ?N. !n. N <= n
                     ==> ?d:real.
                           has_nonnegative_integralB
                             carrier events mu
                             (\x:B.
                                norm
                                  (add (s n x) (neg (h x)))) d /\
                           d < e) /\
          vector_tends zero add neg norm ints z in
   let has_bochner_integralC =
      \(carrier:C->bool) (events:(C->bool)->bool)
       (mu:(C->bool)->bool#real)
       (zero:A) (add:A->A->A) (neg:A->A)
       (smul:real->A->A) (norm:A->real)
       (h:C->A) (z:A).
        ?s:num->C->A ints:num->A.
          (!n. integrable_simple_vectorC
                 carrier events mu zero (s n)) /\
          (!n. simple_vector_integralC
                 carrier mu zero add smul (s n) (ints n)) /\
          (!e. &0 < e
               ==> ?N. !n. N <= n
                     ==> ?d:real.
                           has_nonnegative_integralC
                             carrier events mu
                             (\x:C.
                                norm
                                  (add (s n x) (neg (h x)))) d /\
                           d < e) /\
          vector_tends zero add neg norm ints z in
   let has_bochner_integralBC =
      \(carrier:(B#C)->bool)
       (events:((B#C)->bool)->bool)
       (mu:((B#C)->bool)->bool#real)
       (zero:A) (add:A->A->A) (neg:A->A)
       (smul:real->A->A) (norm:A->real)
       (h:(B#C)->A) (z:A).
        ?s:num->(B#C)->A ints:num->A.
          (!n. integrable_simple_vectorBC
                 carrier events mu zero (s n)) /\
          (!n. simple_vector_integralBC
                 carrier mu zero add smul (s n) (ints n)) /\
          (!e. &0 < e
               ==> ?N. !n. N <= n
                     ==> ?d:real.
                           has_nonnegative_integralBC
                             carrier events mu
                             (\x:B#C.
                                norm
                                  (add (s n x) (neg (h x)))) d /\
                           d < e) /\
          vector_tends zero add neg norm ints z in
   let bochner_integralB =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real)
       (zero:A) (add:A->A->A) (neg:A->A)
       (smul:real->A->A) (norm:A->real)
       (h:B->A).
        if complete_space zero add neg norm /\
           vector_integrableB
             carrier events mu zero add neg norm h
        then @z:A.
               has_bochner_integralB
                 carrier events mu zero add neg smul norm h z
        else zero in
   let bochner_integralC =
      \(carrier:C->bool) (events:(C->bool)->bool)
       (mu:(C->bool)->bool#real)
       (zero:A) (add:A->A->A) (neg:A->A)
       (smul:real->A->A) (norm:A->real)
       (h:C->A).
        if complete_space zero add neg norm /\
           vector_integrableC
             carrier events mu zero add neg norm h
        then @z:A.
               has_bochner_integralC
                 carrier events mu zero add neg smul norm h z
        else zero in
   let bochner_integralBC =
      \(carrier:(B#C)->bool)
       (events:((B#C)->bool)->bool)
       (mu:((B#C)->bool)->bool#real)
       (zero:A) (add:A->A->A) (neg:A->A)
       (smul:real->A->A) (norm:A->real)
       (h:(B#C)->A).
        if complete_space zero add neg norm /\
           vector_integrableBC
             carrier events mu zero add neg norm h
        then @z:A.
               has_bochner_integralBC
                 carrier events mu zero add neg smul norm h z
        else zero in
   !carrierB:B->bool
    carrierC:C->bool
    eventsB:(B->bool)->bool
    eventsC:(C->bool)->bool
    mu:(B->bool)->bool#real
    nu:(C->bool)->bool#real
    zero:A
    add:A->A->A
    neg:A->A
    smul:real->A->A
    norm:A->real
    f:(B#C)->A.
      sfiniteB carrierB eventsB mu /\
      sfiniteC carrierC eventsC nu /\
      normed_real_vector_space zero add neg smul norm /\
      vector_integrableBC
        (product_carrier carrierB carrierC)
        (product_events carrierB carrierC eventsB eventsC)
        (product_measure
           carrierB carrierC eventsB eventsC mu nu)
        zero add neg norm f
      ==>
      bochner_integralBC
        (product_carrier carrierB carrierC)
        (product_events carrierB carrierC eventsB eventsC)
        (product_measure
           carrierB carrierC eventsB eventsC mu nu)
        zero add neg smul norm f =
      bochner_integralB
        carrierB eventsB mu zero add neg smul norm
        (\x:B.
           bochner_integralC
             carrierC eventsC nu zero add neg smul norm
             (\y:C. f (x,y)))`;;
