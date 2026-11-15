(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2027347,
  "Optional stopping theorem": a strongly adapted integrable real-valued
  process over a sigma-finite filtration is a submartingale exactly when
  expected stopped values are monotone for ordered bounded stopping times.
  This file contains no proof.
*)

let Q2027347_OPTIONAL_STOPPING_THEOREM =
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
        (!s. s IN events ==> s SUBSET carrier) /\
        {} IN events /\
        carrier IN events /\
        (!s:A->bool.
           s IN events ==> carrier DIFF s IN events) /\
        (!sets:num->A->bool.
           (!n. sets n IN events)
           ==> {x:A | ?n. x IN sets n} IN events) in
   let measure_space =
      \(carrier:A->bool)
       (events:(A->bool)->bool)
       (mu:(A->bool)->bool#real).
        sigma_algebra carrier events /\
        (!s:A->bool. s SUBSET carrier ==> enonnegative (mu s)) /\
        mu {} = ezero /\
        (!sets:num->A->bool.
           (!n. sets n IN events) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> ?partial:num->bool#real.
                 partial 0 = ezero /\
                 (!n. partial (SUC n) =
                      eadd (partial n) (mu (sets n))) /\
                 esup_sequence partial
                   (mu {x:A | ?n. x IN sets n})) in
   let filtration =
      \(carrier:A->bool)
       (events:(A->bool)->bool)
       (FF:num->(A->bool)->bool).
        (!n. sigma_algebra carrier (FF n) /\ FF n SUBSET events) /\
        (!m n. m <= n ==> FF m SUBSET FF n) in
   let sigma_finite_filtration =
      \(carrier:A->bool)
       (mu:(A->bool)->bool#real)
       (FF:num->(A->bool)->bool).
        !n. ?cover:num->A->bool.
          (!k. cover k IN FF n /\ ~(FST (mu (cover k)))) /\
          (!x:A. x IN carrier ==> ?k. x IN cover k) in
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
        (!x:A. x IN carrier ==> enonnegative (s x)) /\
        FINITE (IMAGE s carrier) /\
        (!c:bool#real. {x:A | x IN carrier /\ s x = c} IN events) in
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
      \(P:(bool#real)->bool)
       (z:bool#real).
        enonnegative z /\
        (!v. P v ==> ele v z) /\
        (!w. enonnegative w /\ (!v. P v ==> ele v w)
             ==> ele z w) in
   let lintegral =
      \(carrier:A->bool)
       (events:(A->bool)->bool)
       (mu:(A->bool)->bool#real)
       (h:A->bool#real).
        @z:bool#real.
          is_supremum
            (\v. ?s:A->bool#real.
                   simple_ennreal carrier events s /\
                   (!x:A. x IN carrier ==> ele (s x) (h x)) /\
                   simple_lintegral carrier mu s v)
            z in
   let simple_scalar =
      \(carrier:A->bool)
       (events:(A->bool)->bool)
       (s:A->real).
        FINITE (IMAGE s carrier) /\
        (!c:real. {x:A | x IN carrier /\ s x = c} IN events) in
   let strongly_measurable_scalar =
      \(carrier:A->bool)
       (events:(A->bool)->bool)
       (h:A->real).
        ?s:num->A->real.
          (!n. simple_scalar carrier events (s n)) /\
          (!x:A. x IN carrier ==> scalar_tends (\n. s n x) (h x)) in
   let ae_strongly_measurable_scalar =
      \(carrier:A->bool)
       (events:(A->bool)->bool)
       (mu:(A->bool)->bool#real)
       (h:A->real).
        ?g:A->real.
          strongly_measurable_scalar carrier events g /\
          almost_everywhere carrier events mu (\x:A. h x = g x) in
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
   let set_integral =
      \(carrier:A->bool)
       (events:(A->bool)->bool)
       (mu:(A->bool)->bool#real)
       (s:A->bool)
       (h:A->real).
        real_integral carrier events mu
          (\x:A. if x IN s then h x else &0) in
   let strongly_adapted =
      \(carrier:A->bool)
       (FF:num->(A->bool)->bool)
       (X:num->A->real).
        !n. strongly_measurable_scalar carrier (FF n) (X n) in
   let submartingale =
      \(carrier:A->bool)
       (events:(A->bool)->bool)
       (mu:(A->bool)->bool#real)
       (FF:num->(A->bool)->bool)
       (X:num->A->real).
        strongly_adapted carrier FF X /\
        (!n. scalar_integrable carrier events mu (X n)) /\
        (!i j s.
           i <= j /\ s IN FF i
           ==> set_integral carrier events mu s (X i) <=
               set_integral carrier events mu s (X j)) in
   let enat_le =
      \(s:num option) (t:num option).
        t = NONE \/
        ?m n. s = SOME m /\ t = SOME n /\ m <= n in
   let stopping_time =
      \(carrier:A->bool)
       (FF:num->(A->bool)->bool)
       (tau:A->num option).
        !n. {x:A | x IN carrier /\ enat_le (tau x) (SOME n)} IN FF n in
   let stopped_value =
      \(X:num->A->real)
       (tau:A->num option)
       (x:A).
        X (@n:num. tau x = SOME n) x in
   !carrier:A->bool
    events:(A->bool)->bool
    mu:(A->bool)->bool#real
    FF:num->(A->bool)->bool
    X:num->A->real.
      measure_space carrier events mu /\
      filtration carrier events FF /\
      sigma_finite_filtration carrier mu FF /\
      strongly_adapted carrier FF X /\
      (!n. scalar_integrable carrier events mu (X n))
      ==>
      (submartingale carrier events mu FF X <=>
       !tau pi:A->num option.
         stopping_time carrier FF tau /\
         stopping_time carrier FF pi /\
         (!x:A. x IN carrier ==> enat_le (tau x) (pi x)) /\
         (?N. !x:A. x IN carrier ==> enat_le (pi x) (SOME N))
         ==> real_integral carrier events mu (stopped_value X tau) <=
             real_integral carrier events mu (stopped_value X pi))`;;
