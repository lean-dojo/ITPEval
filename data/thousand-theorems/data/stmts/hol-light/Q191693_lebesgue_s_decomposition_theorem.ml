(*
  Statement-only formalization of Thousand Theorems corpus artifact Q191693,
  "Lebesgue's decomposition theorem": every s-finite measure decomposes,
  relative to a sigma-finite measure, into a mutually singular measure and
  a measure with a measurable extended-nonnegative density. This file contains
  no proof.
*)

let Q191693_LEBESGUE_S_DECOMPOSITION_THEOREM =
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
   let esum =
      \(u:num->bool#real) (z:bool#real).
        ?partial:num->bool#real.
          partial 0 = ezero /\
          (!n. partial (SUC n) = eadd (partial n) (u n)) /\
          esup_sequence partial z in
   let sigma_algebra =
      \(events:(A->bool)->bool).
        {} IN events /\
        (UNIV:A->bool) IN events /\
        (!s. s IN events ==> (UNIV:A->bool) DIFF s IN events) /\
        (!sets:num->A->bool.
           (!n. sets n IN events)
           ==> {x:A | ?n. x IN sets n} IN events) in
   let measure_space =
      \(events:(A->bool)->bool) (mu:(A->bool)->bool#real).
        sigma_algebra events /\
        (!s:A->bool. enonnegative (mu s)) /\
        mu {} = ezero /\
        (!sets:num->A->bool.
           (!n. sets n IN events) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> esum (\n. mu (sets n))
                 (mu {x:A | ?n. x IN sets n})) in
   let measure_equal =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real)
       (nu:(A->bool)->bool#real).
        !s:A->bool. s IN events ==> mu s = nu s in
   let finite_measure_space =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real).
        measure_space events mu /\ ~(FST (mu (UNIV:A->bool))) in
   let sfinite_measure =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real).
        measure_space events mu /\
        ?parts:num->(A->bool)->bool#real.
          (!n. finite_measure_space events (parts n)) /\
          (!s:A->bool.
             s IN events
             ==> esum (\n. parts n s) (mu s)) in
   let sigma_finite_measure =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real).
        measure_space events mu /\
        ?sets:num->A->bool.
          (!n. sets n IN events /\ ~(FST (mu (sets n)))) /\
          {x:A | ?n. x IN sets n} = (UNIV:A->bool) in
   let sequence_etends =
      \(u:num->bool#real) (l:bool#real).
        enonnegative l /\
        (!n. enonnegative (u n)) /\
        (!e. &0 < e
             ==> ?N. !n. N <= n
                          ==> abs(eembed (u n) - eembed l) < e) in
   let simple_ennreal =
      \(events:(A->bool)->bool) (s:A->bool#real).
        (!x. enonnegative (s x)) /\
        FINITE (IMAGE s (UNIV:A->bool)) /\
        (!c:bool#real. {x:A | s x = c} IN events) in
   let strongly_measurable_ennreal =
      \(events:(A->bool)->bool) (h:A->bool#real).
        (!x. enonnegative (h x)) /\
        ?s:num->A->bool#real.
          (!n. simple_ennreal events (s n)) /\
          (!x. sequence_etends (\n. s n x) (h x)) in
   let finite_esum =
      \(items:(bool#real)->bool)
       (h:(bool#real)->bool#real) (z:bool#real).
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
      \(mu:(A->bool)->bool#real) (s:A->bool#real) (z:bool#real).
        finite_esum (IMAGE s (UNIV:A->bool))
          (\c. emul c (mu {x:A | s x = c})) z in
   let is_supremum =
      \(p:(bool#real)->bool) (z:bool#real).
        enonnegative z /\
        (!v. p v ==> ele v z) /\
        (!w. enonnegative w /\ (!v. p v ==> ele v w)
             ==> ele z w) in
   let lintegral =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real) (f:A->bool#real).
        @z:bool#real.
          is_supremum
            (\v. ?s:A->bool#real.
                   simple_ennreal events s /\
                   (!x. ele (s x) (f x)) /\
                   simple_lintegral mu s v)
            z in
   let with_density =
      \(events:(A->bool)->bool)
       (nu:(A->bool)->bool#real) (f:A->bool#real)
       (s:A->bool).
        lintegral events nu
          (\x:A. if x IN s then f x else ezero) in
   let measure_add =
      \(mu:(A->bool)->bool#real)
       (nu:(A->bool)->bool#real) (s:A->bool).
        eadd (mu s) (nu s) in
   let mutually_singular =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real)
       (nu:(A->bool)->bool#real).
        ?s:A->bool.
          s IN events /\
          mu ((UNIV:A->bool) DIFF s) = ezero /\
          nu s = ezero in
   !events:(A->bool)->bool
    mu:(A->bool)->bool#real
    nu:(A->bool)->bool#real.
      sfinite_measure events mu /\
      sigma_finite_measure events nu
      ==>
      ?xi:(A->bool)->bool#real
       f:A->bool#real.
        measure_space events xi /\
        strongly_measurable_ennreal events f /\
        mutually_singular events xi nu /\
        measure_equal events mu
          (measure_add xi (with_density events nu f))`;;
