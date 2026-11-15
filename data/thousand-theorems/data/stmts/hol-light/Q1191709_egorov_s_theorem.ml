(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1191709,
  "Egorov's theorem": an almost-everywhere convergent countable directed family
  of strongly measurable functions on a measurable set of finite measure
  converges uniformly outside an arbitrarily small measurable subset. This
  file contains no proof.
*)

let Q1191709_EGOROV_S_THEOREM =
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
        ~(FST x) /\ (FST y \/ SND x < SND y) in
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
   let sigma_algebra =
      \(events:(A->bool)->bool).
        events {} /\
        events (:A) /\
        (!s:A->bool.
           events s ==> events ((:A) DIFF s)) /\
        (!sets:num->A->bool.
           (!n. events (sets n))
           ==> events {x:A | ?n. x IN sets n}) in
   let measure_space =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real).
        sigma_algebra events /\
        (!s:A->bool. enonnegative (mu s)) /\
        mu {} = ezero /\
        (!sets:num->A->bool.
           (!n. events (sets n)) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> esum (\n. mu (sets n))
                     (mu {x:A | ?n. x IN sets n})) in
   let almost_everywhere =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real) (P:A->bool).
        ?N:A->bool.
          events N /\
          mu N = ezero /\
          {x:A | ~(P x)} SUBSET N in
   let pseudo_emetric_space =
      \(edist:B->B->bool#real).
        (!x y:B. enonnegative (edist x y)) /\
        (!x:B. edist x x = ezero) /\
        (!x y:B. edist x y = edist y x) /\
        (!x y z:B.
           ele (edist x z) (eadd (edist x y) (edist y z))) in
   let semilattice_sup =
      \(le:I->I->bool) (join:I->I->I).
        (!i:I. le i i) /\
        (!i j k:I. le i j /\ le j k ==> le i k) /\
        (!i j:I. le i j /\ le j i ==> i = j) /\
        (!i j:I. le i (join i j)) /\
        (!i j:I. le j (join i j)) /\
        (!i j k:I. le i k /\ le j k ==> le (join i j) k) in
   let countable_index =
      \(_le:I->I->bool).
        ?code:I->num.
          !i j:I. code i = code j ==> i = j in
   let emetric_tends =
      \(edist:B->B->bool#real) (u:num->B) (l:B).
        !e:real.
          &0 < e
          ==> ?N:num.
                !n:num.
                  N <= n ==> elt (edist (u n) l) (F,e) in
   let simple_function =
      \(events:(A->bool)->bool) (h:A->B).
        FINITE (IMAGE h (:A)) /\
        (!b:B. events {x:A | h x = b}) in
   let strongly_measurable =
      \(events:(A->bool)->bool)
       (edist:B->B->bool#real) (h:A->B).
        ?simple:num->A->B.
          (!n:num. simple_function events (simple n)) /\
          (!x:A.
             emetric_tends edist
               (\n:num. simple n x) (h x)) in
   let index_tends =
      \(le:I->I->bool) (edist:B->B->bool#real)
       (u:I->B) (l:B).
        !e:real.
          &0 < e
          ==> ?j:I.
                !i:I.
                  le j i ==> elt (edist (u i) l) (F,e) in
   let tends_uniformly_on =
      \(le:I->I->bool) (edist:B->B->bool#real)
       (f:I->A->B) (g:A->B) (u:A->bool).
        !e:real.
          &0 < e
          ==> ?j:I.
                !i:I x:A.
                  le j i /\ x IN u
                  ==> elt (edist (f i x) (g x)) (F,e) in
   !events:(A->bool)->bool
    mu:(A->bool)->bool#real
    edist:B->B->bool#real
    le:I->I->bool
    join:I->I->I
    f:I->A->B
    g:A->B
    s:A->bool
    epsilon:real.
      measure_space events mu /\
      pseudo_emetric_space edist /\
      semilattice_sup le join /\
      countable_index le /\
      (!i:I. strongly_measurable events edist (f i)) /\
      strongly_measurable events edist g /\
      events s /\
      ~(FST (mu s)) /\
      almost_everywhere events mu
        (\x:A.
           x IN s
           ==> index_tends le edist
                 (\i:I. f i x) (g x)) /\
      &0 < epsilon
      ==>
      ?t:A->bool.
        t SUBSET s /\
        events t /\
        ele (mu t) (F,epsilon) /\
        tends_uniformly_on le edist f g (s DIFF t)`;;
