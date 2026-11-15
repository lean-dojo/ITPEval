(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3527166
  (thousand-theorems__hol-light__Q3527166), "Steinhaus theorem": a measurable
  set of positive inner-regular left Haar measure in a locally compact
  topological group has its quotient set as a neighborhood of the identity.
  This file contains no proof.
*)

let Q3527166_STEINHAUS_THEOREM =
 `let enonnegative =
      \(z:bool#real).
        (FST z /\ SND z = &0) \/
        (~(FST z) /\ &0 <= SND z) in
   let ezero = (F,&0) in
   let etop = (T,&0) in
   let ele =
      \(x:bool#real) (y:bool#real).
        FST y \/ (~(FST x) /\ SND x <= SND y) in
   let elt =
      \(x:bool#real) (y:bool#real).
        enonnegative x /\
        enonnegative y /\
        ele x y /\
        ~(x = y) in
   let eadd =
      \(x:bool#real) (y:bool#real).
        if FST x \/ FST y
        then etop
        else (F,SND x + SND y) in
   let esup_sequence =
      \(u:num->bool#real) (z:bool#real).
        enonnegative z /\
        (!n:num. enonnegative (u n) /\ ele (u n) z) /\
        (!w:bool#real.
           enonnegative w /\ (!n:num. ele (u n) w)
           ==> ele z w) in
   let esum =
      \(u:num->bool#real) (z:bool#real).
        ?partial:num->bool#real.
          partial 0 = ezero /\
          (!n:num. partial (SUC n) = eadd (partial n) (u n)) /\
          esup_sequence partial z in
   let is_infimum =
      \(p:(bool#real)->bool) (z:bool#real).
        enonnegative z /\
        (!v:bool#real. p v ==> ele z v) /\
        (!w:bool#real.
           enonnegative w /\
           (!v:bool#real. p v ==> ele w v)
           ==> ele w z) in
   let is_topology =
      \(opens:(A->bool)->bool).
        opens {} /\
        opens (UNIV:A->bool) /\
        (!collection:(A->bool)->bool.
           (!u:A->bool. u IN collection ==> opens u)
           ==> opens (UNIONS collection)) /\
        (!u v:A->bool.
           opens u /\ opens v ==> opens (u INTER v)) in
   let is_neighborhood =
      \(opens:(A->bool)->bool) (x:A) (s:A->bool).
        ?u:A->bool.
          opens u /\
          x IN u /\
          u SUBSET s in
   let is_compact =
      \(opens:(A->bool)->bool) (k:A->bool).
        !cover:(A->bool)->bool.
          (!u:A->bool. u IN cover ==> opens u) /\
          k SUBSET UNIONS cover
          ==> ?subcover:(A->bool)->bool.
                subcover SUBSET cover /\
                FINITE subcover /\
                k SUBSET UNIONS subcover in
   let locally_compact =
      \(opens:(A->bool)->bool).
        !x:A. !n:A->bool.
          is_neighborhood opens x n
          ==> ?k:A->bool.
                is_neighborhood opens x k /\
                k SUBSET n /\
                is_compact opens k in
   let group_axioms =
      \(oneG:A) (gmul:A->A->A) (ginv:A->A).
        (!x y z:A. gmul x (gmul y z) = gmul (gmul x y) z) /\
        (!x:A. gmul oneG x = x) /\
        (!x:A. gmul x oneG = x) /\
        (!x:A. gmul (ginv x) x = oneG) /\
        (!x:A. gmul x (ginv x) = oneG) in
   let compatible_group_topology =
      \(gmul:A->A->A) (ginv:A->A)
       (opens:(A->bool)->bool).
        (!x y:A. !u:A->bool.
           opens u /\ gmul x y IN u
           ==> ?v w:A->bool.
                 opens v /\
                 opens w /\
                 x IN v /\
                 y IN w /\
                 (!a b:A.
                    a IN v /\ b IN w ==> gmul a b IN u)) /\
        (!x:A. !u:A->bool.
           opens u /\ ginv x IN u
           ==> ?v:A->bool.
                 opens v /\
                 x IN v /\
                 (!a:A. a IN v ==> ginv a IN u)) in
   let sigma_algebra =
      \(events:(A->bool)->bool).
        events {} /\
        events (UNIV:A->bool) /\
        (!s:A->bool.
           events s ==> events ((UNIV:A->bool) DIFF s)) /\
        (!sets:num->A->bool.
           (!n:num. events (sets n))
           ==> events {x:A | ?n:num. x IN sets n}) in
   let borel_space =
      \(opens:(A->bool)->bool)
       (events:(A->bool)->bool).
        sigma_algebra events /\
        (!u:A->bool. opens u ==> events u) /\
        (!other:(A->bool)->bool.
           sigma_algebra other /\
           (!u:A->bool. opens u ==> other u)
           ==> !s:A->bool. events s ==> other s) in
   let outer_measure =
      \(mu:(A->bool)->bool#real).
        (!s:A->bool. enonnegative (mu s)) /\
        mu {} = ezero /\
        (!s t:A->bool.
           s SUBSET t ==> ele (mu s) (mu t)) /\
        (!sets:num->A->bool. !total:bool#real.
           esum (\n:num. mu (sets n)) total
           ==> ele
                 (mu {x:A | ?n:num. x IN sets n})
                 total) in
   let canonical_extension =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real).
        !s:A->bool.
          ?z:bool#real.
            is_infimum
              (\v:bool#real.
                 ?t:A->bool.
                   events t /\
                   s SUBSET t /\
                   v = mu t)
              z /\
            ele z (mu s) in
   let measure_space =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real).
        sigma_algebra events /\
        outer_measure mu /\
        canonical_extension events mu /\
        (!s t:A->bool.
           events s
           ==> mu t =
               eadd (mu (t INTER s)) (mu (t DIFF s))) /\
        (!sets:num->A->bool.
           (!n:num. events (sets n)) /\
           (!m n:num.
              ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> esum
                 (\n:num. mu (sets n))
                 (mu {x:A | ?n:num. x IN sets n})) in
   let is_haar_measure =
      \(gmul:A->A->A)
       (opens:(A->bool)->bool)
       (events:(A->bool)->bool)
       (mu:(A->bool)->bool#real).
        (!g:A. !s:A->bool.
           events s ==> mu {x:A | gmul g x IN s} = mu s) /\
        (!k:A->bool.
           is_compact opens k ==> ~(mu k = etop)) /\
        (!u:A->bool.
           opens u /\ ~(u = {}) ==> ~(mu u = ezero)) in
   let inner_regular =
      \(opens:(A->bool)->bool)
       (events:(A->bool)->bool)
       (mu:(A->bool)->bool#real).
        !s:A->bool.
          events s
          ==> !r:bool#real.
                elt r (mu s)
                ==> ?k:A->bool.
                      k SUBSET s /\
                      is_compact opens k /\
                      elt r (mu k) in
   let set_div =
      \(gmul:A->A->A) (ginv:A->A)
       (s:A->bool) (t:A->bool).
        {z:A |
           ?x y:A.
             x IN s /\
             y IN t /\
             z = gmul x (ginv y)} in
   !oneG:A.
   !gmul:A->A->A.
   !ginv:A->A.
   !opens:(A->bool)->bool.
   !events:(A->bool)->bool.
   !mu:(A->bool)->bool#real.
   !e:A->bool.
     group_axioms oneG gmul ginv /\
     is_topology opens /\
     compatible_group_topology gmul ginv opens /\
     locally_compact opens /\
     borel_space opens events /\
     measure_space events mu /\
     is_haar_measure gmul opens events mu /\
     inner_regular opens events mu /\
     events e /\
     ~(mu e = ezero)
     ==> is_neighborhood
           opens oneG (set_div gmul ginv e e)`;;
