(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1153584,
  "Monotone convergence theorem": convergence of real integrals for an
  almost-everywhere antitone integrable sequence, and convergence of lower
  Lebesgue integrals for an almost-everywhere monotone sequence of
  extended-nonnegative functions. This file contains no proof.
*)

let Q1153584_MONOTONE_CONVERGENCE_THEOREM =
 `let enonnegative =
      \(z:bool#real).
        (FST z /\ SND z = &0) \/
        (~(FST z) /\ &0 <= SND z) in
   let ezero = (F,&0) in
   let ele =
      \(x:bool#real) (y:bool#real).
        FST y \/ (~(FST x) /\ SND x <= SND y) in
   let eadd =
      \(x:bool#real) (y:bool#real).
        if FST x \/ FST y
        then (T,&0)
        else (F,SND x + SND y) in
   let emul =
      \(x:bool#real) (y:bool#real).
        if (~(FST x) /\ SND x = &0) \/
           (~(FST y) /\ SND y = &0)
        then (F,&0)
        else if FST x \/ FST y
        then (T,&0)
        else (F,SND x * SND y) in
   let eembed =
      \(z:bool#real).
        if FST z then &1 else SND z / (&1 + SND z) in
   let esup_sequence =
      \(u:num->bool#real) (z:bool#real).
        enonnegative z /\
        (!n. enonnegative (u n) /\ ele (u n) z) /\
        (!w. enonnegative w /\ (!n. ele (u n) w) ==> ele z w) in
   let sigma_algebra =
      \(carrier:A->bool) (events:(A->bool)->bool).
        {} IN events /\
        carrier IN events /\
        (!s:A->bool. s IN events ==> s SUBSET carrier) /\
        (!s:A->bool.
           s IN events ==> (carrier DIFF s) IN events) /\
        (!sets:num->A->bool.
           (!n. sets n IN events)
           ==> {x:A | x IN carrier /\ ?n. x IN sets n} IN events) in
   let measure_space =
      \(carrier:A->bool)
       (events:(A->bool)->bool)
       (mu:(A->bool)->bool#real).
        sigma_algebra carrier events /\
        (!s:A->bool. enonnegative (mu s)) /\
        mu {} = ezero /\
        (!s:A->bool. mu s = mu (s INTER carrier)) /\
        (!sets:num->A->bool.
           (!n. sets n IN events) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> ?partial:num->bool#real.
                 partial 0 = ezero /\
                 (!n. partial (SUC n) =
                      eadd (partial n) (mu (sets n))) /\
                 esup_sequence partial
                   (mu {x:A | x IN carrier /\ ?n. x IN sets n})) in
   let almost_everywhere =
      \(carrier:A->bool)
       (events:(A->bool)->bool)
       (mu:(A->bool)->bool#real)
       (P:A->bool).
        ?N:A->bool.
          N IN events /\
          mu N = ezero /\
          {x:A | x IN carrier /\ ~(P x)} SUBSET N in
   let scalar_tends =
      \(u:num->real) (l:real).
        !e. &0 < e
            ==> ?N. !n. N <= n ==> abs(u n - l) < e in
   let sequence_etends =
      \(u:num->bool#real) (l:bool#real).
        enonnegative l /\
        (!n. enonnegative (u n)) /\
        (!e. &0 < e
             ==> ?N. !n. N <= n
                          ==> abs(eembed (u n) - eembed l) < e) in
   let simple_ennreal =
      \(carrier:A->bool)
       (events:(A->bool)->bool)
       (s:A->bool#real).
        (!x. x IN carrier ==> enonnegative (s x)) /\
        FINITE (IMAGE s carrier) /\
        (!c:bool#real.
           {x:A | x IN carrier /\ s x = c} IN events) in
   let finite_esum =
      \(items:(bool#real)->bool)
       (h:(bool#real)->bool#real)
       (z:bool#real).
        FINITE items /\
        (!x. x IN items ==> enonnegative (h x)) /\
        ?n enum partial.
          (!x. x IN items <=> ?i. i < n /\ enum i = x) /\
          (!i j. i < n /\ j < n /\ enum i = enum j ==> i = j) /\
          partial 0 = ezero /\
          (!i. i < n
               ==> partial (SUC i) =
                   eadd (h (enum i)) (partial i)) /\
          z = partial n in
   let simple_lintegral =
      \(carrier:A->bool)
       (mu:(A->bool)->bool#real)
       (s:A->bool#real)
       (z:bool#real).
        finite_esum (IMAGE s carrier)
          (\c. emul c (mu {x:A | x IN carrier /\ s x = c})) z in
   let is_supremum =
      \(p:(bool#real)->bool) (z:bool#real).
        enonnegative z /\
        (!v. p v ==> ele v z) /\
        (!w. enonnegative w /\ (!v. p v ==> ele v w)
             ==> ele z w) in
   let lintegral =
      \(carrier:A->bool)
       (events:(A->bool)->bool)
       (mu:(A->bool)->bool#real)
       (f:A->bool#real).
        @z:bool#real.
          is_supremum
            (\v. ?s:A->bool#real.
                   simple_ennreal carrier events s /\
                   (!x. x IN carrier ==> ele (s x) (f x)) /\
                   simple_lintegral carrier mu s v)
            z in
   let simple_scalar =
      \(carrier:A->bool)
       (events:(A->bool)->bool)
       (s:A->real).
        FINITE (IMAGE s carrier) /\
        (!c:real.
           {x:A | x IN carrier /\ s x = c} IN events) in
   let strongly_measurable_scalar =
      \(carrier:A->bool)
       (events:(A->bool)->bool)
       (h:A->real).
        ?s:num->A->real.
          (!n. simple_scalar carrier events (s n)) /\
          (!x. x IN carrier
               ==> scalar_tends (\n. s n x) (h x)) in
   let ae_strongly_measurable_scalar =
      \(carrier:A->bool)
       (events:(A->bool)->bool)
       (mu:(A->bool)->bool#real)
       (h:A->real).
        ?g:A->real.
          strongly_measurable_scalar carrier events g /\
          almost_everywhere carrier events mu (\x. h x = g x) in
   let strongly_measurable_ennreal =
      \(carrier:A->bool)
       (events:(A->bool)->bool)
       (h:A->bool#real).
        (!x. x IN carrier ==> enonnegative (h x)) /\
        ?s:num->A->bool#real.
          (!n. simple_ennreal carrier events (s n)) /\
          (!x. x IN carrier
               ==> sequence_etends (\n. s n x) (h x)) in
   let ae_measurable_ennreal =
      \(carrier:A->bool)
       (events:(A->bool)->bool)
       (mu:(A->bool)->bool#real)
       (h:A->bool#real).
        (!x. x IN carrier ==> enonnegative (h x)) /\
        ?g:A->bool#real.
          strongly_measurable_ennreal carrier events g /\
          almost_everywhere carrier events mu (\x. h x = g x) in
   let scalar_integrable =
      \(carrier:A->bool)
       (events:(A->bool)->bool)
       (mu:(A->bool)->bool#real)
       (h:A->real).
        ae_strongly_measurable_scalar carrier events mu h /\
        ~(FST
            (lintegral carrier events mu
              (\x:A. (F,abs(h x))))) in
   let real_integral =
      \(carrier:A->bool)
       (events:(A->bool)->bool)
       (mu:(A->bool)->bool#real)
       (h:A->real).
        SND
          (lintegral carrier events mu
            (\x:A. (F,max (h x) (&0)))) -
        SND
          (lintegral carrier events mu
            (\x:A. (F,max (--(h x)) (&0)))) in
   let real_antitone_form =
      !carrier:A->bool
       events:(A->bool)->bool
       mu:(A->bool)->bool#real
       seq:num->A->real
       limit:A->real.
        measure_space carrier events mu /\
        (!n. scalar_integrable carrier events mu (seq n)) /\
        scalar_integrable carrier events mu limit /\
        almost_everywhere carrier events mu
          (\x:A. !m n. m <= n ==> seq n x <= seq m x) /\
        almost_everywhere carrier events mu
          (\x:A. scalar_tends (\n. seq n x) (limit x))
        ==> scalar_tends
              (\n. real_integral carrier events mu (seq n))
              (real_integral carrier events mu limit) in
   let ennreal_monotone_form =
      !carrier:A->bool
       events:(A->bool)->bool
       mu:(A->bool)->bool#real
       seq:num->A->bool#real
       limit:A->bool#real.
        measure_space carrier events mu /\
        (!n x. x IN carrier ==> enonnegative (seq n x)) /\
        (!x. x IN carrier ==> enonnegative (limit x)) /\
        (!n. ae_measurable_ennreal
               carrier events mu (seq n)) /\
        almost_everywhere carrier events mu
          (\x:A. !m n. m <= n ==> ele (seq m x) (seq n x)) /\
        almost_everywhere carrier events mu
          (\x:A. sequence_etends (\n. seq n x) (limit x))
        ==> sequence_etends
              (\n. lintegral carrier events mu (seq n))
              (lintegral carrier events mu limit) in
   real_antitone_form /\ ennreal_monotone_form`;;
