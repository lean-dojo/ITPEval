(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1067156,
  "Dominated convergence theorem": almost-everywhere convergence of strongly
  measurable functions into an arbitrary real normed vector space, under an
  integrable pointwise bound, implies convergence of their Bochner integrals.
  This file contains no proof.
*)

let Q1067156_DOMINATED_CONVERGENCE_THEOREM =
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
   let escale =
      \(c:real) (x:bool#real).
        if c = &0
        then ezero
        else if FST x
             then (T,&0)
             else (F,c * SND x) in
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
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real).
        sigma_algebra carrier events /\
        (!s:B->bool. enonnegative (mu s)) /\
        mu {} = ezero /\
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
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real) (P:B->bool).
        ?N:B->bool.
          events N /\
          mu N = ezero /\
          {x:B | x IN carrier /\ ~(P x)} SUBSET N in
   let scalar_tends =
      \(u:num->real) (l:real).
        !e. &0 < e ==> ?N. !n. N <= n ==> abs(u n - l) < e in
   let normed_real_vector_space =
      \(zero:A) (add:A->A->A) (neg:A->A)
       (smul:real->A->A) (norm:A->real).
        (!x y:A. add x y = add y x) /\
        (!x y z:A. add (add x y) z = add x (add y z)) /\
        (!x:A. add x zero = x) /\
        (!x:A. add x (neg x) = zero) /\
        (!x:A. neg (neg x) = x) /\
        (!x:A. smul (&1) x = x) /\
        (!a b:real x:A. smul (a * b) x = smul a (smul b x)) /\
        (!a b:real x:A.
           smul (a + b) x = add (smul a x) (smul b x)) /\
        (!a:real x y:A.
           smul a (add x y) = add (smul a x) (smul a y)) /\
        (!x:A. smul (&0) x = zero) /\
        (!a:real. smul a zero = zero) /\
        (!x:A. &0 <= norm x) /\
        (!x:A. norm x = &0 <=> x = zero) /\
        (!a:real x:A. norm (smul a x) = abs a * norm x) /\
        (!x y:A. norm (add x y) <= norm x + norm y) in
   let vector_tends =
      \(zero:A) (add:A->A->A) (neg:A->A) (norm:A->real)
       (u:num->A) (l:A).
        !e. &0 < e
            ==> ?N. !n. N <= n
                       ==> norm (add (u n) (neg l)) < e in
   let complete_space =
      \(zero:A) (add:A->A->A) (neg:A->A) (norm:A->real).
        !u:num->A.
          (!e. &0 < e
               ==> ?N. !m n.
                     N <= m /\ N <= n
                     ==> norm (add (u m) (neg (u n))) < e)
          ==> ?l:A. vector_tends zero add neg norm u l in
   let simple_scalar =
      \(carrier:B->bool) (events:(B->bool)->bool) (s:B->real).
        FINITE (IMAGE s carrier) /\
        (!c:real. events {x:B | x IN carrier /\ s x = c}) in
   let simple_vector =
      \(carrier:B->bool) (events:(B->bool)->bool) (s:B->A).
        FINITE (IMAGE s carrier) /\
        (!c:A. events {x:B | x IN carrier /\ s x = c}) in
   let strongly_measurable_scalar =
      \(carrier:B->bool) (events:(B->bool)->bool) (h:B->real).
        ?s:num->B->real.
          (!n. simple_scalar carrier events (s n)) /\
          (!x:B. x IN carrier
                 ==> scalar_tends (\n. s n x) (h x)) in
   let strongly_measurable_vector =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (zero:A) (add:A->A->A) (neg:A->A) (norm:A->real)
       (h:B->A).
        ?s:num->B->A.
          (!n. simple_vector carrier events (s n)) /\
          (!x:B. x IN carrier
                 ==> vector_tends zero add neg norm
                       (\n. s n x) (h x)) in
   let ae_strongly_measurable_scalar =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real) (h:B->real).
        ?g:B->real.
          strongly_measurable_scalar carrier events g /\
          almost_everywhere carrier events mu (\x. h x = g x) in
   let ae_strongly_measurable_vector =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real) (zero:A) (add:A->A->A)
       (neg:A->A) (norm:A->real) (h:B->A).
        ?g:B->A.
          strongly_measurable_vector
            carrier events zero add neg norm g /\
          almost_everywhere carrier events mu (\x. h x = g x) in
   let integrable_simple_vector =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real) (zero:A) (s:B->A).
        simple_vector carrier events s /\
        (!c:A.
           c IN IMAGE s carrier /\ ~(c = zero)
           ==> ~(FST (mu {x:B | x IN carrier /\ s x = c}))) in
   let simple_nonnegative_integral =
      \(carrier:B->bool) (mu:(B->bool)->bool#real)
       (s:B->real) (z:bool#real).
        (!x:B. x IN carrier ==> &0 <= s x) /\
        ?n enum partial:num->bool#real.
          (!c:real.
             c IN IMAGE s carrier <=>
             ?i. i < n /\ enum i = c) /\
          (!i j. i < n /\ j < n /\ enum i = enum j ==> i = j) /\
          partial 0 = ezero /\
          (!i. i < n
               ==> partial (SUC i) =
                   eadd
                     (partial i)
                     (escale
                       (enum i)
                       (mu {x:B |
                              x IN carrier /\ s x = enum i}))) /\
          z = partial n in
   let simple_vector_integral =
      \(carrier:B->bool) (mu:(B->bool)->bool#real)
       (zero:A) (add:A->A->A) (smul:real->A->A)
       (s:B->A) (z:A).
        ?n enum partial.
          (!c:A.
             c IN IMAGE s carrier <=>
             ?i. i < n /\ enum i = c) /\
          (!i j. i < n /\ j < n /\ enum i = enum j ==> i = j) /\
          partial 0 = zero /\
          (!i. i < n
               ==> partial (SUC i) =
                   add
                     (smul
                       (SND (mu {x:B |
                                  x IN carrier /\ s x = enum i}))
                           (enum i))
                     (partial i)) /\
          z = partial n in
   let nonnegative_integral_upper_bound =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real) (h:B->real) (u:bool#real).
        enonnegative u /\
        !s:B->real z:bool#real.
          simple_scalar carrier events s /\
          (!x:B. x IN carrier ==> s x <= h x) /\
          simple_nonnegative_integral carrier mu s z
          ==> ele z u in
   let has_nonnegative_integral =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real) (h:B->real) (r:bool#real).
        enonnegative r /\
        nonnegative_integral_upper_bound carrier events mu h r /\
        (!u:bool#real.
           nonnegative_integral_upper_bound carrier events mu h u
           ==> ele r u) in
   let scalar_integrable =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real) (h:B->real).
        ae_strongly_measurable_scalar carrier events mu h /\
        (?r:bool#real.
           has_nonnegative_integral carrier events mu
             (\x:B. abs(h x)) r /\
           ~(FST r)) in
   let vector_integrable =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real) (zero:A) (add:A->A->A)
       (neg:A->A) (norm:A->real) (h:B->A).
        ae_strongly_measurable_vector
          carrier events mu zero add neg norm h /\
        (?r:bool#real.
           has_nonnegative_integral carrier events mu
             (\x:B. norm(h x)) r /\
           ~(FST r)) in
   let has_bochner_integral =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real) (zero:A) (add:A->A->A)
       (neg:A->A) (smul:real->A->A) (norm:A->real)
       (h:B->A) (z:A).
        ?s:num->B->A ints:num->A.
          (!n. integrable_simple_vector
                 carrier events mu zero (s n)) /\
          (!n. simple_vector_integral
                 carrier mu zero add smul (s n) (ints n)) /\
          (!e. &0 < e
               ==> ?N. !n. N <= n
                     ==> ?d:bool#real.
                           has_nonnegative_integral carrier events mu
                             (\x:B.
                                norm
                                  (add (s n x) (neg (h x)))) d /\
                           ~(FST d) /\
                           SND d < e) /\
          vector_tends zero add neg norm ints z in
   let bochner_integral =
      \(carrier:B->bool) (events:(B->bool)->bool)
       (mu:(B->bool)->bool#real) (zero:A) (add:A->A->A)
       (neg:A->A) (smul:real->A->A) (norm:A->real)
       (h:B->A).
        if complete_space zero add neg norm /\
           vector_integrable
             carrier events mu zero add neg norm h
        then @z:A.
               has_bochner_integral
                 carrier events mu zero add neg smul norm h z
        else zero in
   !carrier:B->bool
    events:(B->bool)->bool
    mu:(B->bool)->bool#real
    zero:A
    add:A->A->A
    neg:A->A
    smul:real->A->A
    norm:A->real
    seq:num->B->A
    f:B->A
    bound:B->real.
      measure_space carrier events mu /\
      normed_real_vector_space zero add neg smul norm /\
      (!n. ae_strongly_measurable_vector
             carrier events mu zero add neg norm (seq n)) /\
      scalar_integrable carrier events mu bound /\
      (!n. almost_everywhere carrier events mu
             (\x:B. norm(seq n x) <= bound x)) /\
      almost_everywhere carrier events mu
        (\x:B. vector_tends zero add neg norm
                 (\n. seq n x) (f x))
      ==> vector_tends zero add neg norm
            (\n. bochner_integral
                   carrier events mu zero add neg smul norm (seq n))
            (bochner_integral
               carrier events mu zero add neg smul norm f)`;;
