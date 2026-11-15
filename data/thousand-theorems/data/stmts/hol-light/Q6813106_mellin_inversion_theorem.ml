(*
  Statement-only formalization of Thousand Theorems corpus artifact Q6813106,
  "Mellin inversion theorem": for a Banach-valued function on the reals, its
  inverse Mellin transform recovers the function at a positive continuity
  point under Mellin and vertical integrability assumptions. This file
  contains no proof.
*)

let q6813106_output = open_out "/dev/null";;
Format.pp_set_formatter_out_channel Format.std_formatter q6813106_output;;
let q6813106_formatter = Format.formatter_of_out_channel q6813106_output;;
let q6813106_previous_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file q6813106_formatter path);;
let q6813106_loaded =
  Toploop.use_file q6813106_formatter "Library/transc.ml";;
Hol_loader.file_loader := q6813106_previous_loader;;
Format.pp_print_flush q6813106_formatter ();;
if not q6813106_loaded then failwith "Unable to load transcendental library";;

let Q6813106_MELLIN_INVERSION_THEOREM =
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
   let cadd =
      \(z:real#real) (w:real#real).
        (FST z + FST w,SND z + SND w) in
   let cmul =
      \(z:real#real) (w:real#real).
        (FST z * FST w - SND z * SND w,
         FST z * SND w + SND z * FST w) in
   let cmod =
      \(z:real#real).
        sqrt(FST z pow 2 + SND z pow 2) in
   let cone = (&1,&0) in
   let czero = (&0,&0) in
   let positive_cpow =
      \(t:real) (z:real#real).
        (exp(ln t * FST z) * cos(ln t * SND z),
         exp(ln t * FST z) * sin(ln t * SND z)) in
   let sigma_algebra =
      \(events:(real->bool)->bool).
        events {} /\
        events (:real) /\
        (!s:real->bool. events s ==> events ((:real) DIFF s)) /\
        (!sets:num->real->bool.
           (!n. events (sets n))
           ==> events {x:real | ?n. x IN sets n}) in
   let measure_space =
      \(events:(real->bool)->bool)
       (mu:(real->bool)->bool#real).
        sigma_algebra events /\
        (!s:real->bool. enonnegative (mu s)) /\
        mu {} = ezero /\
        (!sets:num->real->bool.
           (!n. events (sets n)) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> ?partial:num->bool#real.
                 partial 0 = ezero /\
                 (!n. partial (SUC n) =
                      eadd (partial n) (mu (sets n))) /\
                 esup_sequence partial
                   (mu {x:real | ?n. x IN sets n})) in
   let metric_open =
      \(s:real->bool).
        !x:real.
          x IN s
          ==> ?epsilon:real.
                &0 < epsilon /\
                !y:real. abs(y - x) < epsilon ==> y IN s in
   let borel_space =
      \(events:(real->bool)->bool).
        sigma_algebra events /\
        (!s:real->bool. metric_open s ==> events s) /\
        (!other:(real->bool)->bool.
           sigma_algebra other /\
           (!s:real->bool. metric_open s ==> other s)
           ==> !s:real->bool. events s ==> other s) in
   let lebesgue_measure =
      \(mu:(real->bool)->bool#real).
        !a b:real.
          mu {x:real | a < x /\ x <= b} =
          (F,if a <= b then b - a else &0) in
   let almost_everywhere =
      \(carrier:real->bool) (events:(real->bool)->bool)
       (mu:(real->bool)->bool#real) (P:real->bool).
        ?N:real->bool.
          events N /\
          mu N = ezero /\
          {x:real | x IN carrier /\ ~(P x)} SUBSET N in
   let scalar_tends =
      \(u:num->real) (l:real).
        !epsilon:real.
          &0 < epsilon
          ==> ?N:num. !n:num.
                N <= n ==> abs(u n - l) < epsilon in
   let vector_tends =
      \(zeroE:E) (addE:E->E->E) (negE:E->E)
       (normE:E->real) (u:num->E) (l:E).
        !epsilon:real.
          &0 < epsilon
          ==> ?N:num. !n:num.
                N <= n
                ==> normE (addE (u n) (negE l)) < epsilon in
   let complex_normed_vector_space =
      \(zeroE:E) (addE:E->E->E) (negE:E->E)
       (csmul:(real#real)->E->E) (normE:E->real).
        (!x y:E. addE x y = addE y x) /\
        (!x y z:E. addE (addE x y) z = addE x (addE y z)) /\
        (!x:E. addE x zeroE = x) /\
        (!x:E. addE x (negE x) = zeroE) /\
        (!x:E. negE (negE x) = x) /\
        (!x:E. csmul cone x = x) /\
        (!a b:real#real x:E.
           csmul (cmul a b) x = csmul a (csmul b x)) /\
        (!a b:real#real x:E.
           csmul (cadd a b) x =
           addE (csmul a x) (csmul b x)) /\
        (!a:real#real x y:E.
           csmul a (addE x y) =
           addE (csmul a x) (csmul a y)) /\
        (!x:E. csmul czero x = zeroE) /\
        (!a:real#real. csmul a zeroE = zeroE) /\
        (!x:E. &0 <= normE x) /\
        (!x:E. normE x = &0 <=> x = zeroE) /\
        (!a:real#real x:E.
           normE (csmul a x) = cmod a * normE x) /\
        (!x y:E. normE (addE x y) <= normE x + normE y) in
   let complete_space =
      \(zeroE:E) (addE:E->E->E) (negE:E->E)
       (normE:E->real).
        !u:num->E.
          (!epsilon:real.
             &0 < epsilon
             ==> ?N:num. !m n:num.
                   N <= m /\ N <= n
                   ==> normE
                         (addE (u m) (negE (u n))) < epsilon)
          ==> ?l:E. vector_tends zeroE addE negE normE u l in
   let simple_scalar =
      \(carrier:real->bool) (events:(real->bool)->bool)
       (s:real->real).
        FINITE (IMAGE s carrier) /\
        (!c:real.
           events {x:real | x IN carrier /\ s x = c}) in
   let simple_vector =
      \(carrier:real->bool) (events:(real->bool)->bool)
       (s:real->E).
        FINITE (IMAGE s carrier) /\
        (!c:E.
           events {x:real | x IN carrier /\ s x = c}) in
   let strongly_measurable_scalar =
      \(carrier:real->bool) (events:(real->bool)->bool)
       (h:real->real).
        ?s:num->real->real.
          (!n. simple_scalar carrier events (s n)) /\
          (!x:real.
             x IN carrier
             ==> scalar_tends (\n. s n x) (h x)) in
   let strongly_measurable_vector =
      \(carrier:real->bool) (events:(real->bool)->bool)
       (zeroE:E) (addE:E->E->E) (negE:E->E)
       (normE:E->real) (h:real->E).
        ?s:num->real->E.
          (!n. simple_vector carrier events (s n)) /\
          (!x:real.
             x IN carrier
             ==> vector_tends zeroE addE negE normE
                   (\n. s n x) (h x)) in
   let ae_strongly_measurable_scalar =
      \(carrier:real->bool) (events:(real->bool)->bool)
       (mu:(real->bool)->bool#real) (h:real->real).
        ?g:real->real.
          strongly_measurable_scalar carrier events g /\
          almost_everywhere carrier events mu
            (\x. h x = g x) in
   let ae_strongly_measurable_vector =
      \(carrier:real->bool) (events:(real->bool)->bool)
       (mu:(real->bool)->bool#real)
       (zeroE:E) (addE:E->E->E) (negE:E->E)
       (normE:E->real) (h:real->E).
        ?g:real->E.
          strongly_measurable_vector
            carrier events zeroE addE negE normE g /\
          almost_everywhere carrier events mu
            (\x. h x = g x) in
   let integrable_simple_vector =
      \(carrier:real->bool) (events:(real->bool)->bool)
       (mu:(real->bool)->bool#real) (zeroE:E) (s:real->E).
        simple_vector carrier events s /\
        (!c:E.
           c IN IMAGE s carrier /\ ~(c = zeroE)
           ==> ~(FST
                  (mu {x:real | x IN carrier /\ s x = c}))) in
   let simple_nonnegative_integral =
      \(carrier:real->bool) (mu:(real->bool)->bool#real)
       (s:real->real) (z:bool#real).
        (!x:real. x IN carrier ==> &0 <= s x) /\
        ?n:num enum:num->real partial:num->bool#real.
          (!c:real.
             c IN IMAGE s carrier <=>
             ?i:num. i < n /\ enum i = c) /\
          (!i j:num.
             i < n /\ j < n /\ enum i = enum j ==> i = j) /\
          partial 0 = ezero /\
          (!i:num.
             i < n
             ==> partial (SUC i) =
                 eadd
                   (partial i)
                   (escale
                     (enum i)
                     (mu {x:real |
                            x IN carrier /\ s x = enum i}))) /\
          z = partial n in
   let simple_vector_integral =
      \(carrier:real->bool) (mu:(real->bool)->bool#real)
       (zeroE:E) (addE:E->E->E)
       (csmul:(real#real)->E->E) (s:real->E) (z:E).
        ?n:num enum:num->E partial:num->E.
          (!c:E.
             c IN IMAGE s carrier <=>
             ?i:num. i < n /\ enum i = c) /\
          (!i j:num.
             i < n /\ j < n /\ enum i = enum j ==> i = j) /\
          partial 0 = zeroE /\
          (!i:num.
             i < n
             ==> partial (SUC i) =
                 addE
                   (csmul
                     (SND
                       (mu {x:real |
                              x IN carrier /\ s x = enum i}),&0)
                     (enum i))
                   (partial i)) /\
          z = partial n in
   let nonnegative_integral_upper_bound =
      \(carrier:real->bool) (events:(real->bool)->bool)
       (mu:(real->bool)->bool#real)
       (h:real->real) (u:bool#real).
        enonnegative u /\
        !s:real->real z:bool#real.
          simple_scalar carrier events s /\
          (!x:real. x IN carrier ==> s x <= h x) /\
          simple_nonnegative_integral carrier mu s z
          ==> ele z u in
   let has_nonnegative_integral =
      \(carrier:real->bool) (events:(real->bool)->bool)
       (mu:(real->bool)->bool#real)
       (h:real->real) (r:bool#real).
        enonnegative r /\
        nonnegative_integral_upper_bound
          carrier events mu h r /\
        (!u:bool#real.
           nonnegative_integral_upper_bound
             carrier events mu h u
           ==> ele r u) in
   let vector_integrable =
      \(carrier:real->bool) (events:(real->bool)->bool)
       (mu:(real->bool)->bool#real)
       (zeroE:E) (addE:E->E->E) (negE:E->E)
       (normE:E->real) (h:real->E).
        ae_strongly_measurable_vector
          carrier events mu zeroE addE negE normE h /\
        (?r:bool#real.
           has_nonnegative_integral carrier events mu
             (\x:real. normE(h x)) r /\
           ~(FST r)) in
   let has_bochner_integral =
      \(carrier:real->bool) (events:(real->bool)->bool)
       (mu:(real->bool)->bool#real)
       (zeroE:E) (addE:E->E->E) (negE:E->E)
       (csmul:(real#real)->E->E) (normE:E->real)
       (h:real->E) (z:E).
        ?s:num->real->E ints:num->E.
          (!n. integrable_simple_vector
                 carrier events mu zeroE (s n)) /\
          (!n. simple_vector_integral
                 carrier mu zeroE addE csmul (s n) (ints n)) /\
          (!epsilon:real.
             &0 < epsilon
             ==> ?N:num. !n:num.
                   N <= n
                   ==> ?d:bool#real.
                         has_nonnegative_integral
                           carrier events mu
                           (\x:real.
                              normE
                                (addE (s n x) (negE (h x)))) d /\
                         ~(FST d) /\
                         SND d < epsilon) /\
          vector_tends zeroE addE negE normE ints z in
   let bochner_integral =
      \(carrier:real->bool) (events:(real->bool)->bool)
       (mu:(real->bool)->bool#real)
       (zeroE:E) (addE:E->E->E) (negE:E->E)
       (csmul:(real#real)->E->E) (normE:E->real)
       (h:real->E).
        if complete_space zeroE addE negE normE /\
           vector_integrable
             carrier events mu zeroE addE negE normE h
        then @z:E.
               has_bochner_integral
                 carrier events mu zeroE addE negE csmul normE h z
        else zeroE in
   let continuous_at =
      \(addE:E->E->E) (negE:E->E) (normE:E->real)
       (f:real->E) (x:real).
        !epsilon:real.
          &0 < epsilon
          ==> ?delta:real.
                &0 < delta /\
                !y:real.
                  abs(y - x) < delta
                  ==> normE
                        (addE (f y) (negE (f x))) < epsilon in
   let mellin_convergent =
      \(events:(real->bool)->bool)
       (mu:(real->bool)->bool#real)
       (zeroE:E) (addE:E->E->E) (negE:E->E)
       (csmul:(real#real)->E->E) (normE:E->real)
       (f:real->E) (s:real#real).
        vector_integrable
          {t:real | &0 < t} events mu zeroE addE negE normE
          (\t:real.
             csmul
               (positive_cpow t (FST s - &1,SND s))
               (f t)) in
   let mellin =
      \(events:(real->bool)->bool)
       (mu:(real->bool)->bool#real)
       (zeroE:E) (addE:E->E->E) (negE:E->E)
       (csmul:(real#real)->E->E) (normE:E->real)
       (f:real->E) (s:real#real).
        bochner_integral
          {t:real | &0 < t} events mu
          zeroE addE negE csmul normE
          (\t:real.
             csmul
               (positive_cpow t (FST s - &1,SND s))
               (f t)) in
   let vertical_integrable =
      \(events:(real->bool)->bool)
       (mu:(real->bool)->bool#real)
       (zeroE:E) (addE:E->E->E) (negE:E->E)
       (normE:E->real) (transform:(real#real)->E) (sigma:real).
        vector_integrable
          (:real) events mu zeroE addE negE normE
          (\y:real. transform (sigma,y)) in
   let mellin_inv =
      \(events:(real->bool)->bool)
       (mu:(real->bool)->bool#real)
       (zeroE:E) (addE:E->E->E) (negE:E->E)
       (csmul:(real#real)->E->E) (normE:E->real)
       (sigma:real) (transform:(real#real)->E) (x:real).
        csmul (&1 / (&2 * pi),&0)
          (bochner_integral
            (:real) events mu zeroE addE negE csmul normE
            (\y:real.
               csmul
                 (positive_cpow x (--sigma,--y))
                 (transform (sigma,y)))) in
   !events:(real->bool)->bool
    mu:(real->bool)->bool#real
    zeroE:E
    addE:E->E->E
    negE:E->E
    csmul:(real#real)->E->E
    normE:E->real.
      borel_space events /\
      measure_space events mu /\
      lebesgue_measure mu /\
      complex_normed_vector_space zeroE addE negE csmul normE /\
      complete_space zeroE addE negE normE
      ==>
      !sigma:real f:real->E x:real.
        &0 < x /\
        mellin_convergent
          events mu zeroE addE negE csmul normE f (sigma,&0) /\
        vertical_integrable
          events mu zeroE addE negE normE
          (mellin
            events mu zeroE addE negE csmul normE f)
          sigma /\
        continuous_at addE negE normE f x
        ==> mellin_inv
              events mu zeroE addE negE csmul normE sigma
              (mellin
                events mu zeroE addE negE csmul normE f) x =
            f x`;;
