(*
  Statement-only formalization of Thousand Theorems corpus artifact Q179467,
  "Fourier theorem": Fourier inversion for integrable Banach-valued functions
  on finite-dimensional real inner-product spaces, pointwise at continuity
  points and extensionally for continuous functions. This file contains no
  proof.
*)

let q179467_output = open_out "/dev/null";;
let q179467_formatter = Format.formatter_of_out_channel q179467_output;;
let q179467_previous_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file q179467_formatter path);;
let q179467_loaded =
  Toploop.use_file q179467_formatter "Library/transc.ml";;
Hol_loader.file_loader := q179467_previous_loader;;
Format.pp_print_flush q179467_formatter ();;
close_out q179467_output;;
if not q179467_loaded then failwith "Unable to load transcendental library";;

let Q179467_FOURIER_THEOREM =
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
   let sigma_algebra =
      \(events:(V->bool)->bool).
        events {} /\
        events (:V) /\
        (!s:V->bool. events s ==> events ((:V) DIFF s)) /\
        (!sets:num->V->bool.
           (!n. events (sets n))
           ==> events {x:V | ?n. x IN sets n}) in
   let measure_space =
      \(events:(V->bool)->bool)
       (mu:(V->bool)->bool#real).
        sigma_algebra events /\
        (!s:V->bool. enonnegative (mu s)) /\
        mu {} = ezero /\
        (!sets:num->V->bool.
           (!n. events (sets n)) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> ?partial:num->bool#real.
                 partial 0 = ezero /\
                 (!n. partial (SUC n) =
                      eadd (partial n) (mu (sets n))) /\
                 esup_sequence partial
                   (mu {x:V | ?n. x IN sets n})) in
   let almost_everywhere =
      \(events:(V->bool)->bool)
       (mu:(V->bool)->bool#real) (P:V->bool).
        ?N:V->bool.
          events N /\
          mu N = ezero /\
          {x:V | ~(P x)} SUBSET N in
   let real_vector_space =
      \(zeroV:V) (addV:V->V->V) (negV:V->V)
       (smulV:real->V->V).
        (!x y:V. addV x y = addV y x) /\
        (!x y z:V. addV (addV x y) z = addV x (addV y z)) /\
        (!x:V. addV x zeroV = x) /\
        (!x:V. addV x (negV x) = zeroV) /\
        (!x:V. negV (negV x) = x) /\
        (!x:V. smulV (&1) x = x) /\
        (!a b:real x:V.
           smulV (a * b) x = smulV a (smulV b x)) /\
        (!a b:real x:V.
           smulV (a + b) x = addV (smulV a x) (smulV b x)) /\
        (!a:real x y:V.
           smulV a (addV x y) = addV (smulV a x) (smulV a y)) /\
        (!x:V. smulV (&0) x = zeroV) /\
        (!a:real. smulV a zeroV = zeroV) in
   let real_inner_product =
      \(zeroV:V) (addV:V->V->V) (smulV:real->V->V)
       (inner:V->V->real).
        (!x y z:V.
           inner (addV x y) z = inner x z + inner y z) /\
        (!a:real x y:V.
           inner (smulV a x) y = a * inner x y) /\
        (!x y:V. inner x y = inner y x) /\
        (!x:V. &0 <= inner x x) /\
        (!x:V. inner x x = &0 <=> x = zeroV) in
   let vnorm =
      \(inner:V->V->real) (x:V).
        sqrt(inner x x) in
   let finite_linear_combination =
      \(zeroV:V) (addV:V->V->V) (smulV:real->V->V)
       (n:num) (basis:num->V) (coeff:num->real) (x:V).
        ?partial:num->V.
          partial 0 = zeroV /\
          (!i. i < n
               ==> partial (SUC i) =
                   addV (partial i) (smulV (coeff i) (basis i))) /\
          partial n = x in
   let finite_dimensional =
      \(zeroV:V) (addV:V->V->V) (smulV:real->V->V).
        ?n:num basis:num->V.
          (!x:V.
             ?coeff:num->real.
               finite_linear_combination
                 zeroV addV smulV n basis coeff x) /\
          (!coeff:num->real.
             finite_linear_combination
               zeroV addV smulV n basis coeff zeroV
             ==> !i. i < n ==> coeff i = &0) in
   let metric_open =
      \(addV:V->V->V) (negV:V->V) (inner:V->V->real)
       (s:V->bool).
        !x:V.
          x IN s
          ==> ?epsilon:real.
                &0 < epsilon /\
                !y:V.
                  vnorm inner (addV y (negV x)) < epsilon
                  ==> y IN s in
   let borel_space =
      \(addV:V->V->V) (negV:V->V) (inner:V->V->real)
       (events:(V->bool)->bool).
        sigma_algebra events /\
        (!s:V->bool.
           metric_open addV negV inner s ==> events s) /\
        (!other:(V->bool)->bool.
           sigma_algebra other /\
           (!s:V->bool.
              metric_open addV negV inner s ==> other s)
           ==> !s:V->bool. events s ==> other s) in
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
      \(events:(V->bool)->bool) (s:V->real).
        FINITE (IMAGE s (:V)) /\
        (!c:real. events {x:V | s x = c}) in
   let simple_vector =
      \(events:(V->bool)->bool) (s:V->E).
        FINITE (IMAGE s (:V)) /\
        (!c:E. events {x:V | s x = c}) in
   let strongly_measurable_scalar =
      \(events:(V->bool)->bool) (h:V->real).
        ?s:num->V->real.
          (!n. simple_scalar events (s n)) /\
          (!x:V. scalar_tends (\n. s n x) (h x)) in
   let strongly_measurable_vector =
      \(events:(V->bool)->bool)
       (zeroE:E) (addE:E->E->E) (negE:E->E)
       (normE:E->real) (h:V->E).
        ?s:num->V->E.
          (!n. simple_vector events (s n)) /\
          (!x:V.
             vector_tends zeroE addE negE normE
               (\n. s n x) (h x)) in
   let ae_strongly_measurable_scalar =
      \(events:(V->bool)->bool)
       (mu:(V->bool)->bool#real) (h:V->real).
        ?g:V->real.
          strongly_measurable_scalar events g /\
          almost_everywhere events mu (\x. h x = g x) in
   let ae_strongly_measurable_vector =
      \(events:(V->bool)->bool)
       (mu:(V->bool)->bool#real)
       (zeroE:E) (addE:E->E->E) (negE:E->E)
       (normE:E->real) (h:V->E).
        ?g:V->E.
          strongly_measurable_vector
            events zeroE addE negE normE g /\
          almost_everywhere events mu (\x. h x = g x) in
   let integrable_simple_scalar =
      \(events:(V->bool)->bool)
       (mu:(V->bool)->bool#real) (s:V->real).
        simple_scalar events s /\
        (!c:real.
           c IN IMAGE s (:V) /\ ~(c = &0)
           ==> ~(FST (mu {x:V | s x = c}))) in
   let integrable_simple_vector =
      \(events:(V->bool)->bool)
       (mu:(V->bool)->bool#real) (zeroE:E) (s:V->E).
        simple_vector events s /\
        (!c:E.
           c IN IMAGE s (:V) /\ ~(c = zeroE)
           ==> ~(FST (mu {x:V | s x = c}))) in
   let simple_scalar_integral =
      \(mu:(V->bool)->bool#real) (s:V->real) (z:real).
        ?n:num enum:num->real partial:num->real.
          (!c:real.
             c IN IMAGE s (:V) <=> ?i:num. i < n /\ enum i = c) /\
          (!i j:num.
             i < n /\ j < n /\ enum i = enum j ==> i = j) /\
          partial 0 = &0 /\
          (!i:num.
             i < n
             ==> partial (SUC i) =
                 SND (mu {x:V | s x = enum i}) * enum i +
                 partial i) /\
          z = partial n in
   let simple_vector_integral =
      \(mu:(V->bool)->bool#real)
       (zeroE:E) (addE:E->E->E)
       (csmul:(real#real)->E->E) (s:V->E) (z:E).
        ?n:num enum:num->E partial:num->E.
          (!c:E.
             c IN IMAGE s (:V) <=> ?i:num. i < n /\ enum i = c) /\
          (!i j:num.
             i < n /\ j < n /\ enum i = enum j ==> i = j) /\
          partial 0 = zeroE /\
          (!i:num.
             i < n
             ==> partial (SUC i) =
                 addE
                   (csmul
                     (SND (mu {x:V | s x = enum i}),&0)
                     (enum i))
                   (partial i)) /\
          z = partial n in
   let nonnegative_integral_upper_bound =
      \(events:(V->bool)->bool)
       (mu:(V->bool)->bool#real) (h:V->real) (u:real).
        !s:V->real z:real.
          integrable_simple_scalar events mu s /\
          (!x:V. &0 <= s x /\ s x <= h x) /\
          simple_scalar_integral mu s z
          ==> z <= u in
   let has_nonnegative_integral =
      \(events:(V->bool)->bool)
       (mu:(V->bool)->bool#real) (h:V->real) (r:real).
        &0 <= r /\
        nonnegative_integral_upper_bound events mu h r /\
        (!u:real.
           &0 <= u /\
           nonnegative_integral_upper_bound events mu h u
           ==> r <= u) in
   let scalar_integrable =
      \(events:(V->bool)->bool)
       (mu:(V->bool)->bool#real) (h:V->real).
        ae_strongly_measurable_scalar events mu h /\
        (?r:real.
           has_nonnegative_integral events mu
             (\x:V. abs(h x)) r) in
   let vector_integrable =
      \(events:(V->bool)->bool)
       (mu:(V->bool)->bool#real)
       (zeroE:E) (addE:E->E->E) (negE:E->E)
       (normE:E->real) (h:V->E).
        ae_strongly_measurable_vector
          events mu zeroE addE negE normE h /\
        (?r:real.
           has_nonnegative_integral events mu
             (\x:V. normE(h x)) r) in
   let has_bochner_integral =
      \(events:(V->bool)->bool)
       (mu:(V->bool)->bool#real)
       (zeroE:E) (addE:E->E->E) (negE:E->E)
       (csmul:(real#real)->E->E) (normE:E->real)
       (h:V->E) (z:E).
        ?s:num->V->E ints:num->E.
          (!n. integrable_simple_vector events mu zeroE (s n)) /\
          (!n. simple_vector_integral
                 mu zeroE addE csmul (s n) (ints n)) /\
          (!epsilon:real.
             &0 < epsilon
             ==> ?N:num. !n:num.
                   N <= n
                   ==> ?d:real.
                         has_nonnegative_integral events mu
                           (\x:V.
                              normE
                                (addE (s n x) (negE (h x)))) d /\
                         d < epsilon) /\
          vector_tends zeroE addE negE normE ints z in
   let bochner_integral =
      \(events:(V->bool)->bool)
       (mu:(V->bool)->bool#real)
       (zeroE:E) (addE:E->E->E) (negE:E->E)
       (csmul:(real#real)->E->E) (normE:E->real)
       (h:V->E).
        if complete_space zeroE addE negE normE /\
           vector_integrable
             events mu zeroE addE negE normE h
        then @z:E.
               has_bochner_integral
                 events mu zeroE addE negE csmul normE h z
        else zeroE in
   let normalized_add_haar_measure =
      \(zeroV:V) (addV:V->V->V) (negV:V->V)
       (inner:V->V->real)
       (events:(V->bool)->bool)
       (mu:(V->bool)->bool#real).
        (!a:V s:V->bool.
           events s ==> mu (IMAGE (addV a) s) = mu s) /\
        (!R:real.
           ~(FST
             (mu {x:V | vnorm inner x <= R}))) /\
        has_nonnegative_integral events mu
          (\x:V. exp(--pi * vnorm inner x pow 2)) (&1) in
   let continuous_at =
      \(addV:V->V->V) (negV:V->V) (inner:V->V->real)
       (addE:E->E->E) (negE:E->E) (normE:E->real)
       (f:V->E) (v:V).
        !epsilon:real.
          &0 < epsilon
          ==> ?delta:real.
                &0 < delta /\
                !w:V.
                  vnorm inner (addV w (negV v)) < delta
                  ==> normE
                        (addE (f w) (negE (f v))) < epsilon in
   let continuous =
      \(addV:V->V->V) (negV:V->V) (inner:V->V->real)
       (addE:E->E->E) (negE:E->E) (normE:E->real)
       (f:V->E).
        !v:V.
          continuous_at
            addV negV inner addE negE normE f v in
   let fourier_character =
      \(inner:V->V->real) (sign:real) (v:V) (w:V).
        (cos(&2 * pi * inner v w),
         sign * sin(&2 * pi * inner v w)) in
   let fourier =
      \(events:(V->bool)->bool)
       (mu:(V->bool)->bool#real)
       (zeroE:E) (addE:E->E->E) (negE:E->E)
       (csmul:(real#real)->E->E) (normE:E->real)
       (inner:V->V->real) (f:V->E) (v:V).
        bochner_integral
          events mu zeroE addE negE csmul normE
          (\w:V.
             csmul (fourier_character inner (-- &1) v w) (f w)) in
   let fourier_inv =
      \(events:(V->bool)->bool)
       (mu:(V->bool)->bool#real)
       (zeroE:E) (addE:E->E->E) (negE:E->E)
       (csmul:(real#real)->E->E) (normE:E->real)
       (inner:V->V->real) (f:V->E) (v:V).
        bochner_integral
          events mu zeroE addE negE csmul normE
          (\w:V.
             csmul (fourier_character inner (&1) v w) (f w)) in
   !zeroV:V
    addV:V->V->V
    negV:V->V
    smulV:real->V->V
    inner:V->V->real
    events:(V->bool)->bool
    mu:(V->bool)->bool#real
    zeroE:E
    addE:E->E->E
    negE:E->E
    csmul:(real#real)->E->E
    normE:E->real.
      real_vector_space zeroV addV negV smulV /\
      real_inner_product zeroV addV smulV inner /\
      finite_dimensional zeroV addV smulV /\
      borel_space addV negV inner events /\
      measure_space events mu /\
      normalized_add_haar_measure
        zeroV addV negV inner events mu /\
      complex_normed_vector_space zeroE addE negE csmul normE /\
      complete_space zeroE addE negE normE
      ==>
      ((!f:V->E v:V.
          vector_integrable
            events mu zeroE addE negE normE f /\
          vector_integrable
            events mu zeroE addE negE normE
            (fourier
              events mu zeroE addE negE csmul normE inner f) /\
          continuous_at
            addV negV inner addE negE normE f v
          ==> fourier_inv
                events mu zeroE addE negE csmul normE inner
                (fourier
                  events mu zeroE addE negE csmul normE inner f) v =
              f v) /\
       (!f:V->E.
          continuous
            addV negV inner addE negE normE f /\
          vector_integrable
            events mu zeroE addE negE normE f /\
          vector_integrable
            events mu zeroE addE negE normE
            (fourier
              events mu zeroE addE negE csmul normE inner f)
          ==> fourier_inv
                events mu zeroE addE negE csmul normE inner
                (fourier
                  events mu zeroE addE negE csmul normE inner f) =
              f))`;;
