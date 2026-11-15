(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2275191,
  "Lebesgue differentiation theorem": for an a.e.-measurable extended-
  nonnegative function with finite integral, its integral averages over sets
  shrinking along a Vitali family converge to the function almost everywhere.
  This file contains no proof.
*)

let Q2275191_LEBESGUE_DIFFERENTIATION_THEOREM =
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
        else (F,&1 / SND x) in
   let ediv =
      \(x:bool#real) (y:bool#real). emul x (einv y) in
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
        events {} /\
        events (UNIV:A->bool) /\
        (!s:A->bool.
           events s ==> events ((UNIV:A->bool) DIFF s)) /\
        (!sets:num->A->bool.
           (!n. events (sets n))
           ==> events {x:A | ?n. x IN sets n}) in
   let outer_measure =
      \(mu:(A->bool)->bool#real).
        (!s:A->bool. enonnegative (mu s)) /\
        mu {} = ezero /\
        (!s t:A->bool. s SUBSET t ==> ele (mu s) (mu t)) /\
        (!sets:num->A->bool total:bool#real.
           esum (\n. mu (sets n)) total
           ==> ele (mu {x:A | ?n. x IN sets n}) total) in
   let measure_space =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real).
        sigma_algebra events /\
        outer_measure mu /\
        (!s:A->bool.
           ?t:A->bool.
             events t /\
             s SUBSET t /\
             mu t = mu s) /\
        (!sets:num->A->bool.
           (!n. events (sets n)) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> esum (\n. mu (sets n))
                 (mu {x:A | ?n. x IN sets n})) in
   let almost_everywhere =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real) (p:A->bool).
        ?n:A->bool.
          events n /\
          mu n = ezero /\
          {x:A | ~(p x)} SUBSET n in
   let is_pseudometric =
      \(d:A->A->real).
        (!x y:A. &0 <= d x y) /\
        (!x:A. d x x = &0) /\
        (!x y:A. d x y = d y x) /\
        (!x y z:A. d x z <= d x y + d y z) in
   let open_ball =
      \(d:A->A->real) (x:A) (r:real).
        {y:A | d y x < r} in
   let closed_ball =
      \(d:A->A->real) (x:A) (r:real).
        {y:A | d y x <= r} in
   let metric_open =
      \(d:A->A->real) (u:A->bool).
        !x:A.
          x IN u
          ==> ?r:real.
                &0 < r /\
                open_ball d x r SUBSET u in
   let second_countable =
      \(d:A->A->real).
        ?basis:(A->bool)->bool.
          COUNTABLE basis /\
          (!b:A->bool. b IN basis ==> metric_open d b) /\
          (!u:A->bool x:A.
             metric_open d u /\ x IN u
             ==> ?b:A->bool.
                   b IN basis /\ x IN b /\ b SUBSET u) in
   let borel_space =
      \(d:A->A->real) (events:(A->bool)->bool).
        sigma_algebra events /\
        (!u:A->bool. metric_open d u ==> events u) /\
        (!other:(A->bool)->bool.
           sigma_algebra other /\
           (!u:A->bool. metric_open d u ==> other u)
           ==> !s:A->bool. events s ==> other s) in
   let locally_finite_measure =
      \(d:A->A->real) (mu:(A->bool)->bool#real).
        !x:A.
          ?u:A->bool.
            metric_open d u /\
            x IN u /\
            ~(FST (mu u)) in
   let interior_nonempty =
      \(d:A->A->real) (s:A->bool).
        ?x:A r:real.
          &0 < r /\
          open_ball d x r SUBSET s in
   let fine_subfamily_on =
      \(d:A->A->real)
       (sets_at:A->(A->bool)->bool)
       (f:A->(A->bool)->bool)
       (s:A->bool).
        (!x:A a:A->bool.
           x IN s /\ f x a ==> sets_at x a) /\
        (!x:A.
           x IN s
           ==> !r:real.
                 &0 < r
                 ==> ?a:A->bool.
                       f x a /\
                       a SUBSET closed_ball d x r) in
   let disjoint_subfamily_cover =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real)
       (f:A->(A->bool)->bool)
       (s:A->bool).
        ?chosen:(A#(A->bool))->bool.
          (!p:A#(A->bool).
             p IN chosen
             ==> FST p IN s /\ f (FST p) (SND p)) /\
          (!p q:A#(A->bool).
             p IN chosen /\ q IN chosen /\ ~(p = q)
             ==> DISJOINT (SND p) (SND q)) /\
          mu
            (s DIFF
             {y:A |
                ?p:A#(A->bool).
                  p IN chosen /\ y IN SND p}) = ezero in
   let vitali_family =
      \(d:A->A->real)
       (events:(A->bool)->bool)
       (mu:(A->bool)->bool#real)
       (sets_at:A->(A->bool)->bool).
        (!x:A a:A->bool.
           sets_at x a
           ==> events a /\ interior_nonempty d a) /\
        (!x:A r:real.
           &0 < r
           ==> ?a:A->bool.
                 sets_at x a /\
                 a SUBSET closed_ball d x r) /\
        (!f:A->(A->bool)->bool s:A->bool.
           fine_subfamily_on d sets_at f s
           ==> disjoint_subfamily_cover events mu f s) in
   let sequence_etends =
      \(u:num->bool#real) (l:bool#real).
        enonnegative l /\
        (!n. enonnegative (u n)) /\
        (!e:real.
           &0 < e
           ==> ?n:num.
                 !k:num.
                   n <= k
                   ==> abs(eembed (u k) - eembed l) < e) in
   let simple_ennreal =
      \(events:(A->bool)->bool) (s:A->bool#real).
        (!x:A. enonnegative (s x)) /\
        FINITE (IMAGE s (UNIV:A->bool)) /\
        (!c:bool#real. events {x:A | s x = c}) in
   let measurable_ennreal =
      \(events:(A->bool)->bool) (f:A->bool#real).
        (!x:A. enonnegative (f x)) /\
        ?s:num->A->bool#real.
          (!n. simple_ennreal events (s n)) /\
          (!x:A. sequence_etends (\n. s n x) (f x)) in
   let aemeasurable_ennreal =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real)
       (f:A->bool#real).
        (!x:A. enonnegative (f x)) /\
        ?g:A->bool#real.
          measurable_ennreal events g /\
          almost_everywhere events mu (\x:A. f x = g x) in
   let finite_esum =
      \(items:(bool#real)->bool)
       (h:(bool#real)->bool#real) (z:bool#real).
        FINITE items /\
        (!x:bool#real. x IN items ==> enonnegative (h x)) /\
        ?n:num enum:num->bool#real partial:num->bool#real.
          (!x:bool#real.
             x IN items <=> ?i:num. i < n /\ enum i = x) /\
          (!i j:num.
             i < n /\ j < n /\ enum i = enum j ==> i = j) /\
          partial 0 = ezero /\
          (!i:num.
             i < n
             ==> partial (SUC i) =
                 eadd (h (enum i)) (partial i)) /\
          z = partial n in
   let simple_lintegral =
      \(mu:(A->bool)->bool#real)
       (s:A->bool#real) (z:bool#real).
        finite_esum (IMAGE s (UNIV:A->bool))
          (\c:bool#real. emul c (mu {x:A | s x = c})) z in
   let is_supremum =
      \(p:(bool#real)->bool) (z:bool#real).
        enonnegative z /\
        (!v:bool#real. p v ==> ele v z) /\
        (!w:bool#real.
           enonnegative w /\
           (!v:bool#real. p v ==> ele v w)
           ==> ele z w) in
   let lintegral =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real)
       (f:A->bool#real).
        @z:bool#real.
          is_supremum
            (\v:bool#real.
               ?s:A->bool#real.
                 simple_ennreal events s /\
                 (!x:A. ele (s x) (f x)) /\
                 simple_lintegral mu s v)
            z in
   let set_lintegral =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real)
       (f:A->bool#real)
       (a:A->bool).
        lintegral events mu
          (\x:A. if x IN a then f x else ezero) in
   let tends_along_vitali =
      \(d:A->A->real)
       (sets_at:A->(A->bool)->bool)
       (x:A)
       (g:(A->bool)->bool#real)
       (l:bool#real).
        enonnegative l /\
        (!a:A->bool. sets_at x a ==> enonnegative (g a)) /\
        (!e:real.
           &0 < e
           ==> ?r:real.
                 &0 < r /\
                 !a:A->bool.
                   sets_at x a /\
                   a SUBSET closed_ball d x r
                   ==> abs(eembed (g a) - eembed l) < e) in
   !d:A->A->real
    events:(A->bool)->bool
    mu:(A->bool)->bool#real
    sets_at:A->(A->bool)->bool
    f:A->bool#real.
      is_pseudometric d /\
      second_countable d /\
      borel_space d events /\
      measure_space events mu /\
      locally_finite_measure d mu /\
      vitali_family d events mu sets_at /\
      aemeasurable_ennreal events mu f /\
      ~(lintegral events mu f = etop)
      ==>
      almost_everywhere events mu
        (\x:A.
           tends_along_vitali d sets_at x
             (\a:A->bool.
                ediv (set_lintegral events mu f a) (mu a))
             (f x))`;;
