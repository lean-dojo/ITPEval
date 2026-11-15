(*
  Statement-only formalization of Thousand Theorems corpus artifact Q11352023,
  "Vitali convergence theorem": for a sequence of functions on an arbitrary
  measure space, convergence in measure together with uniform Lp integrability
  and uniform Lp tightness is equivalent to convergence in Lp. This file
  contains no proof.
*)

let Q11352023_VITALI_CONVERGENCE_THEOREM =
 `let enonnegative =
      \(z:bool#real).
        (FST z /\ SND z = &0) \/
        (~(FST z) /\ &0 <= SND z) in
   let ezero = (F,&0) in
   let eone = (F,&1) in
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
   let emul =
      \(x:bool#real) (y:bool#real).
        if (~(FST x) /\ SND x = &0) \/
           (~(FST y) /\ SND y = &0)
        then ezero
        else if FST x \/ FST y
        then etop
        else (F,SND x * SND y) in
   let rpow =
      \(x:real) (q:real).
        if x = &0
        then if q = &0 then &1 else &0
        else exp(q * log x) in
   let erpow =
      \(z:bool#real) (q:real).
        if q = &0
        then eone
        else if FST z
        then etop
        else (F,rpow (SND z) q) in
   let esup_sequence =
      \(u:num->bool#real) (z:bool#real).
        enonnegative z /\
        (!n. enonnegative (u n) /\ ele (u n) z) /\
        (!w. enonnegative w /\ (!n. ele (u n) w) ==> ele z w) in
   let sigma_algebra =
      \(carrier:B->bool) (events:(B->bool)->bool).
        events {} /\
        events carrier /\
        (!s:B->bool. events s ==> s SUBSET carrier) /\
        (!s:B->bool.
           events s ==> events (carrier DIFF s)) /\
        (!sets:num->B->bool.
           (!n. events (sets n))
           ==> events {x:B | ?n. x IN sets n}) in
   let measure_space =
      \(carrier:B->bool)
       (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real).
        sigma_algebra carrier events /\
        (!s:B->bool. enonnegative (mu s)) /\
        mu {} = ezero /\
        (!s:B->bool. mu s = mu (s INTER carrier)) /\
        (!s t:B->bool.
           s SUBSET t ==> ele (mu s) (mu t)) /\
        (!s:B->bool. !z:bool#real.
           enonnegative z /\
           (!t:B->bool.
              events t /\ (s INTER carrier) SUBSET t
              ==> ele z (mu t))
           ==> ele z (mu s)) /\
        (!sets:num->B->bool.
           (!n. events (sets n)) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> ?partial:num->bool#real.
                 partial 0 = ezero /\
                 (!n. partial (SUC n) =
                      eadd (partial n) (mu (sets n))) /\
                 esup_sequence partial
                   (mu {x:B | ?n. x IN sets n})) in
   let almost_everywhere =
      \(carrier:B->bool)
       (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real) (P:B->bool).
        ?N:B->bool.
          events N /\
          mu N = ezero /\
          {x:B | x IN carrier /\ ~(P x)} SUBSET N in
   let normed_add_comm_group =
      \(zero:A) (add:A->A->A) (neg:A->A) (norm:A->real).
        (!x y:A. add x y = add y x) /\
        (!x y z:A. add (add x y) z = add x (add y z)) /\
        (!x:A. add x zero = x) /\
        (!x:A. add x (neg x) = zero) /\
        (!x:A. &0 <= norm x) /\
        (!x:A. norm x = &0 <=> x = zero) /\
        (!x:A. norm (neg x) = norm x) /\
        (!x y:A. norm (add x y) <= norm x + norm y) in
   let vector_tends =
      \(add:A->A->A) (neg:A->A) (norm:A->real)
       (u:num->A) (l:A).
        !e:real.
          &0 < e
          ==> ?N:num. !n:num.
                N <= n
                ==> norm (add (u n) (neg l)) < e in
   let simple_vector =
      \(carrier:B->bool)
       (events:(B->bool)->bool) (s:B->A).
        FINITE (IMAGE s carrier) /\
        (!c:A. events {x:B | x IN carrier /\ s x = c}) in
   let strongly_measurable_vector =
      \(carrier:B->bool)
       (events:(B->bool)->bool)
       (add:A->A->A) (neg:A->A) (norm:A->real)
       (h:B->A).
        ?s:num->B->A.
          (!n. simple_vector carrier events (s n)) /\
          (!x:B.
             x IN carrier
             ==> vector_tends add neg norm
                   (\n. s n x) (h x)) in
   let ae_strongly_measurable_vector =
      \(carrier:B->bool)
       (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real)
       (add:A->A->A) (neg:A->A) (norm:A->real)
       (h:B->A).
        ?g:B->A.
          strongly_measurable_vector
            carrier events add neg norm g /\
          almost_everywhere
            carrier events mu (\x:B. h x = g x) in
   let simple_function =
      \(carrier:B->bool)
       (events:(B->bool)->bool) (s:B->bool#real).
        (!x:B. x IN carrier ==> enonnegative (s x)) /\
        FINITE (IMAGE s carrier) /\
        (!c:bool#real.
           events {x:B | x IN carrier /\ s x = c}) in
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
      \(carrier:B->bool)
       (mu:(B->bool)->bool#real)
       (s:B->bool#real) (z:bool#real).
        finite_esum (IMAGE s carrier)
          (\c. emul c
                 (mu {x:B | x IN carrier /\ s x = c})) z in
   let is_supremum =
      \(P:(bool#real)->bool) (z:bool#real).
        enonnegative z /\
        (!v. P v ==> ele v z) /\
        (!w. enonnegative w /\ (!v. P v ==> ele v w)
             ==> ele z w) in
   let lintegral =
      \(carrier:B->bool)
       (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real)
       (h:B->bool#real).
        @z:bool#real.
          is_supremum
            (\v. ?s:B->bool#real.
                   simple_function carrier events s /\
                   (!x:B.
                      x IN carrier ==> ele (s x) (h x)) /\
                   simple_lintegral carrier mu s v)
            z in
   let indicator =
      \(zero:A) (s:B->bool) (h:B->A) (x:B).
        if x IN s then h x else zero in
   let difference =
      \(add:A->A->A) (neg:A->A)
       (h:B->A) (k:B->A) (x:B).
        add (h x) (neg (k x)) in
   let lp_norm =
      \(carrier:B->bool)
       (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real)
       (norm:A->real) (p:real) (h:B->A).
        erpow
          (lintegral carrier events mu
            (\x:B. (F,rpow (norm (h x)) p)))
          (&1 / p) in
   let mem_lp =
      \(carrier:B->bool)
       (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real)
       (add:A->A->A) (neg:A->A) (norm:A->real)
       (p:real) (h:B->A).
        ae_strongly_measurable_vector
          carrier events mu add neg norm h /\
        elt (lp_norm carrier events mu norm p h) etop in
   let etends_zero =
      \(u:num->bool#real).
        !e:real.
          &0 < e
          ==> ?N:num. !n:num.
                N <= n ==> elt (u n) (F,e) in
   let tends_in_measure =
      \(carrier:B->bool)
       (mu:(B->bool)->bool#real)
       (add:A->A->A) (neg:A->A) (norm:A->real)
       (seq:num->B->A) (g:B->A).
        !e:real.
          &0 < e
          ==> etends_zero
                (\n:num.
                   mu {x:B |
                     x IN carrier /\
                     e <= norm
                       (add (seq n x) (neg (g x)))}) in
   let unif_integrable =
      \(carrier:B->bool)
       (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real)
       (zero:A) (norm:A->real) (p:real)
       (seq:num->B->A).
        !e:real.
          &0 < e
          ==> ?d:real.
                &0 < d /\
                !n:num. !s:B->bool.
                  events s /\
                  ele (mu s) (F,d)
                  ==> ele
                        (lp_norm carrier events mu norm p
                          (indicator zero s (seq n)))
                        (F,e) in
   let unif_tight =
      \(carrier:B->bool)
       (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real)
       (zero:A) (norm:A->real) (p:real)
       (seq:num->B->A).
        !e:real.
          &0 < e
          ==> ?s:B->bool.
                s SUBSET carrier /\
                ~(FST (mu s)) /\
                !n:num.
                  ele
                    (lp_norm carrier events mu norm p
                      (indicator zero (carrier DIFF s) (seq n)))
                    (F,e) in
   !carrier:B->bool
    events:(B->bool)->bool
    mu:(B->bool)->bool#real
    zero:A
    add:A->A->A
    neg:A->A
    norm:A->real
    p:real
    seq:num->B->A
    g:B->A.
      measure_space carrier events mu /\
      normed_add_comm_group zero add neg norm /\
      &1 <= p /\
      (!n:num.
         mem_lp carrier events mu add neg norm p (seq n)) /\
      mem_lp carrier events mu add neg norm p g
      ==>
      (tends_in_measure carrier mu add neg norm seq g /\
       unif_integrable carrier events mu zero norm p seq /\
       unif_tight carrier events mu zero norm p seq
       <=>
       etends_zero
         (\n:num.
            lp_norm carrier events mu norm p
              (difference add neg (seq n) g)))`;;
