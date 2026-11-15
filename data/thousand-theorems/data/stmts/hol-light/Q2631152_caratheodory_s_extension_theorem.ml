(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2631152
  (thousand-theorems__hol-light__Q2631152), "Carathéodory's extension theorem":
  a sigma-subadditive additive content on a semiring of sets agrees, on every
  semiring set, with its Carathéodory measure on the generated sigma-algebra.
  This file contains no proof.
*)

let Q2631152_CARATHEODORY_S_EXTENSION_THEOREM =
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
   let finite_esum =
      \(n:num) (u:num->bool#real) (z:bool#real).
        ?partial:num->bool#real.
          partial 0 = ezero /\
          (!i. i < n
               ==> partial (SUC i) = eadd (partial i) (u i)) /\
          z = partial n in
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
   let is_infimum =
      \(p:(bool#real)->bool) (z:bool#real).
        enonnegative z /\
        (!v. p v ==> enonnegative v /\ ele z v) /\
        (!w. enonnegative w /\ (!v. p v ==> ele w v)
             ==> ele w z) in
   let set_semiring =
      \(C:(A->bool)->bool).
        C {} /\
        (!s t:A->bool.
           C s /\ C t ==> C (s INTER t)) /\
        (!s t:A->bool.
           C s /\ C t
           ==> ?n:num pieces:num->A->bool.
                 (!i. i < n ==> C (pieces i)) /\
                 (!i j.
                    i < n /\ j < n /\ ~(i = j)
                    ==> DISJOINT (pieces i) (pieces j)) /\
                 s DIFF t =
                   {x:A | ?i:num. i < n /\ x IN pieces i}) in
   let additive_content =
      \(C:(A->bool)->bool)
       (m:(A->bool)->bool#real).
        (!s:A->bool. enonnegative (m s)) /\
        m {} = ezero /\
        (!n:num sets:num->A->bool.
           (!i. i < n ==> C (sets i)) /\
           (!i j.
              i < n /\ j < n /\ ~(i = j)
              ==> DISJOINT (sets i) (sets j)) /\
           C {x:A | ?i:num. i < n /\ x IN sets i}
           ==> ?total:bool#real.
                 finite_esum n (\i. m (sets i)) total /\
                 m {x:A | ?i:num. i < n /\ x IN sets i} =
                 total) in
   let sigma_subadditive =
      \(C:(A->bool)->bool)
       (m:(A->bool)->bool#real).
        !sets:num->A->bool.
          (!n. C (sets n)) /\
          C {x:A | ?n:num. x IN sets n}
          ==> ?total:bool#real.
                esum (\n. m (sets n)) total /\
                ele (m {x:A | ?n:num. x IN sets n}) total in
   let sigma_algebra =
      \(events:(A->bool)->bool).
        events {} /\
        events (:A) /\
        (!s:A->bool.
           events s ==> events ((:A) DIFF s)) /\
        (!sets:num->A->bool.
           (!n. events (sets n))
           ==> events {x:A | ?n:num. x IN sets n}) in
   let generated_event =
      \(C:(A->bool)->bool) (s:A->bool).
        !events:(A->bool)->bool.
          sigma_algebra events /\
          (!u:A->bool. C u ==> events u)
          ==> events s in
   let generated_space =
      \(C:(A->bool)->bool)
       (events:(A->bool)->bool).
        sigma_algebra events /\
        (!s:A->bool. events s <=> generated_event C s) in
   let extended_content =
      \(C:(A->bool)->bool)
       (m:(A->bool)->bool#real)
       (s:A->bool).
        @z:bool#real.
          is_infimum
            (\v:bool#real.
               ?t:A->bool.
                 C t /\ s SUBSET t /\ v = m t)
            z in
   let cover_sum =
      \(C:(A->bool)->bool)
       (m:(A->bool)->bool#real)
       (s:A->bool) (v:bool#real).
        ?sets:num->A->bool.
          s SUBSET {x:A | ?n:num. x IN sets n} /\
          esum (\n. extended_content C m (sets n)) v in
   let induced_outer_value =
      \(C:(A->bool)->bool)
       (m:(A->bool)->bool#real)
       (s:A->bool).
        @z:bool#real.
          is_infimum (cover_sum C m s) z in
   let trimmed_outer_value =
      \(events:(A->bool)->bool)
       (outer:(A->bool)->bool#real)
       (s:A->bool).
        @z:bool#real.
          is_infimum
            (\v:bool#real.
               ?t:A->bool.
                 events t /\ s SUBSET t /\ v = outer t)
            z in
   let caratheodory_measure =
      \(C:(A->bool)->bool)
       (events:(A->bool)->bool)
       (m:(A->bool)->bool#real)
       (s:A->bool).
        trimmed_outer_value events (induced_outer_value C m) s in
   !C:(A->bool)->bool
    events:(A->bool)->bool
    m:(A->bool)->bool#real
    s:A->bool.
      set_semiring C /\
      additive_content C m /\
      generated_space C events /\
      sigma_subadditive C m /\
      C s
      ==> caratheodory_measure C events m s = m s`;;
