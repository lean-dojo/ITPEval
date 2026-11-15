(*
  Statement-only formalization of Thousand Theorems corpus artifact Q258374,
  "Carathéodory's theorem (measure theory)": every outer measure admits a
  measurable space whose measurable sets are exactly those satisfying
  Carathéodory's splitting criterion. This file contains no proof.
*)

let Q258374_CARATHEODORY_S_THEOREM_MEASURE_THEORY =
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
   let outer_measure =
      \(mu:(A->bool)->bool#real).
        (!s:A->bool. enonnegative (mu s)) /\
        mu {} = ezero /\
        (!s t:A->bool. s SUBSET t ==> ele (mu s) (mu t)) /\
        (!sets:num->A->bool.
           ?total:bool#real.
             esum (\n. mu (sets n)) total /\
             ele (mu {x:A | ?n. x IN sets n}) total) in
   let sigma_algebra =
      \(events:(A->bool)->bool).
        events {} /\
        events (:A) /\
        (!s:A->bool.
           events s ==> events ((:A) DIFF s)) /\
        (!sets:num->A->bool.
           (!n. events (sets n))
           ==> events {x:A | ?n. x IN sets n}) in
   !mu:(A->bool)->bool#real.
      outer_measure mu
      ==> ?events:(A->bool)->bool.
            sigma_algebra events /\
            (!s:A->bool.
               events s <=>
               !t:A->bool.
                 mu t =
                 eadd (mu (t INTER s)) (mu (t DIFF s)))`;;
