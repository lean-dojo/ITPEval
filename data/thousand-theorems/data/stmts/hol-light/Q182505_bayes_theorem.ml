(*
  Statement-only formalization of Thousand Theorems corpus artifact Q182505,
  "Bayes' theorem" (thousand-theorems__hol-light__Q182505): for two measurable
  events in an arbitrary finite measure space, conditional probability obeys
  Bayes' identity, including zero-measure conditioning events. This file
  contains no proof.
*)

let Q182505_BAYES_THEOREM =
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
   let einv =
      \(x:bool#real).
        if FST x
        then ezero
        else if SND x = &0
        then etop
        else (F,inv(SND x)) in
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
        (!u:A->bool.
           u IN events ==> (UNIV:A->bool) DIFF u IN events) /\
        (!sets:num->A->bool.
           (!n. sets n IN events)
           ==> {x:A | ?n. x IN sets n} IN events) in
   let measure_space =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real).
        sigma_algebra events /\
        (!u:A->bool. enonnegative (mu u)) /\
        mu {} = ezero /\
        (!sets:num->A->bool.
           (!n. sets n IN events) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> esum
                 (\n. mu (sets n))
                 (mu {x:A | ?n. x IN sets n})) in
   let finite_measure_space =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real).
        measure_space events mu /\
        ~(FST (mu (UNIV:A->bool))) in
   let conditional_probability =
      \(mu:(A->bool)->bool#real)
       (event:A->bool)
       (given:A->bool).
        emul (einv (mu given)) (mu (given INTER event)) in
   !events:(A->bool)->bool
    mu:(A->bool)->bool#real
    s:A->bool
    t:A->bool.
      finite_measure_space events mu /\
      s IN events /\
      t IN events
      ==>
      conditional_probability mu t s =
      emul
        (emul
          (einv (mu s))
          (conditional_probability mu s t))
        (mu t)`;;
