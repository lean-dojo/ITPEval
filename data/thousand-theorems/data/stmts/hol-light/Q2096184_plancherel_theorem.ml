(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2096184,
  "Plancherel theorem": the Fourier transform preserves the integral of the
  pointwise complex inner product of Schwartz maps on a finite-dimensional
  real inner-product space. This file contains no proof.
*)

let q2096184_output = open_out "/dev/null";;
let q2096184_formatter = Format.formatter_of_out_channel q2096184_output;;
let q2096184_previous_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file q2096184_formatter path);;
let q2096184_loaded =
  Toploop.use_file q2096184_formatter "Library/transc.ml";;
Hol_loader.file_loader := q2096184_previous_loader;;
Format.pp_print_flush q2096184_formatter ();;
close_out q2096184_output;;
if not q2096184_loaded then failwith "Unable to load transcendental library";;

let Q2096184_PLANCHEREL_THEOREM =
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
   let cnj =
      \(z:real#real). (FST z,--(SND z)) in
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
       (innerV:V->V->real).
        (!x y z:V.
           innerV (addV x y) z = innerV x z + innerV y z) /\
        (!a:real x y:V.
           innerV (smulV a x) y = a * innerV x y) /\
        (!x y:V. innerV x y = innerV y x) /\
        (!x:V. &0 <= innerV x x) /\
        (!x:V. innerV x x = &0 <=> x = zeroV) in
   let vnorm =
      \(innerV:V->V->real) (x:V).
        sqrt(innerV x x) in
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
      \(addV:V->V->V) (negV:V->V) (innerV:V->V->real)
       (s:V->bool).
        !x:V.
          x IN s
          ==> ?epsilon:real.
                &0 < epsilon /\
                !y:V.
                  vnorm innerV (addV y (negV x)) < epsilon
                  ==> y IN s in
   let borel_space =
      \(addV:V->V->V) (negV:V->V) (innerV:V->V->real)
       (events:(V->bool)->bool).
        sigma_algebra events /\
        (!s:V->bool.
           metric_open addV negV innerV s ==> events s) /\
        (!other:(V->bool)->bool.
           sigma_algebra other /\
           (!s:V->bool.
              metric_open addV negV innerV s ==> other s)
           ==> !s:V->bool. events s ==> other s) in
   let complex_vector_space =
      \(zeroH:H) (addH:H->H->H) (negH:H->H)
       (csmul:(real#real)->H->H).
        (!x y:H. addH x y = addH y x) /\
        (!x y z:H. addH (addH x y) z = addH x (addH y z)) /\
        (!x:H. addH x zeroH = x) /\
        (!x:H. addH x (negH x) = zeroH) /\
        (!x:H. negH (negH x) = x) /\
        (!x:H. csmul cone x = x) /\
        (!a b:real#real x:H.
           csmul (cmul a b) x = csmul a (csmul b x)) /\
        (!a b:real#real x:H.
           csmul (cadd a b) x =
           addH (csmul a x) (csmul b x)) /\
        (!a:real#real x y:H.
           csmul a (addH x y) =
           addH (csmul a x) (csmul a y)) /\
        (!x:H. csmul czero x = zeroH) /\
        (!a:real#real. csmul a zeroH = zeroH) in
   let complex_inner_product =
      \(zeroH:H) (addH:H->H->H)
       (csmul:(real#real)->H->H)
       (innerH:H->H->real#real).
        (!x y z:H.
           innerH (addH x y) z =
           cadd (innerH x z) (innerH y z)) /\
        (!a:real#real x y:H.
           innerH (csmul a x) y =
           cmul (cnj a) (innerH x y)) /\
        (!x y:H. innerH x y = cnj (innerH y x)) /\
        (!x:H.
           SND (innerH x x) = &0 /\
           &0 <= FST (innerH x x)) /\
        (!x:H. innerH x x = czero <=> x = zeroH) in
   let hnorm =
      \(innerH:H->H->real#real) (x:H).
        sqrt(FST (innerH x x)) in
   let scalar_tends =
      \(u:num->real) (l:real).
        !epsilon:real.
          &0 < epsilon
          ==> ?N:num. !n:num.
                N <= n ==> abs(u n - l) < epsilon in
   let vector_tends =
      \(zeroH:H) (addH:H->H->H) (negH:H->H)
       (innerH:H->H->real#real) (u:num->H) (l:H).
        !epsilon:real.
          &0 < epsilon
          ==> ?N:num. !n:num.
                N <= n
                ==> hnorm innerH (addH (u n) (negH l)) < epsilon in
   let complete_space =
      \(zeroH:H) (addH:H->H->H) (negH:H->H)
       (innerH:H->H->real#real).
        !u:num->H.
          (!epsilon:real.
             &0 < epsilon
             ==> ?N:num. !m n:num.
                   N <= m /\ N <= n
                   ==> hnorm innerH
                         (addH (u m) (negH (u n))) < epsilon)
          ==> ?l:H.
                vector_tends zeroH addH negH innerH u l in
   let simple_scalar =
      \(events:(V->bool)->bool) (s:V->real).
        FINITE (IMAGE s (:V)) /\
        (!c:real. events {x:V | s x = c}) in
   let simple_vector =
      \(events:(V->bool)->bool) (s:V->H).
        FINITE (IMAGE s (:V)) /\
        (!c:H. events {x:V | s x = c}) in
   let strongly_measurable_scalar =
      \(events:(V->bool)->bool) (h:V->real).
        ?s:num->V->real.
          (!n. simple_scalar events (s n)) /\
          (!x:V. scalar_tends (\n. s n x) (h x)) in
   let strongly_measurable_vector =
      \(events:(V->bool)->bool)
       (zeroH:H) (addH:H->H->H) (negH:H->H)
       (innerH:H->H->real#real) (h:V->H).
        ?s:num->V->H.
          (!n. simple_vector events (s n)) /\
          (!x:V.
             vector_tends zeroH addH negH innerH
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
       (zeroH:H) (addH:H->H->H) (negH:H->H)
       (innerH:H->H->real#real) (h:V->H).
        ?g:V->H.
          strongly_measurable_vector
            events zeroH addH negH innerH g /\
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
       (mu:(V->bool)->bool#real) (zeroH:H) (s:V->H).
        simple_vector events s /\
        (!c:H.
           c IN IMAGE s (:V) /\ ~(c = zeroH)
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
       (zeroH:H) (addH:H->H->H)
       (csmul:(real#real)->H->H) (s:V->H) (z:H).
        ?n:num enum:num->H partial:num->H.
          (!c:H.
             c IN IMAGE s (:V) <=> ?i:num. i < n /\ enum i = c) /\
          (!i j:num.
             i < n /\ j < n /\ enum i = enum j ==> i = j) /\
          partial 0 = zeroH /\
          (!i:num.
             i < n
             ==> partial (SUC i) =
                 addH
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
       (zeroH:H) (addH:H->H->H) (negH:H->H)
       (innerH:H->H->real#real) (h:V->H).
        ae_strongly_measurable_vector
          events mu zeroH addH negH innerH h /\
        (?r:real.
           has_nonnegative_integral events mu
             (\x:V. hnorm innerH (h x)) r) in
   let has_bochner_integral =
      \(events:(V->bool)->bool)
       (mu:(V->bool)->bool#real)
       (zeroH:H) (addH:H->H->H) (negH:H->H)
       (csmul:(real#real)->H->H)
       (innerH:H->H->real#real) (h:V->H) (z:H).
        ?s:num->V->H ints:num->H.
          (!n. integrable_simple_vector events mu zeroH (s n)) /\
          (!n. simple_vector_integral
                 mu zeroH addH csmul (s n) (ints n)) /\
          (!epsilon:real.
             &0 < epsilon
             ==> ?N:num. !n:num.
                   N <= n
                   ==> ?d:real.
                         has_nonnegative_integral events mu
                           (\x:V.
                              hnorm innerH
                                (addH (s n x) (negH (h x)))) d /\
                         d < epsilon) /\
          vector_tends zeroH addH negH innerH ints z in
   let bochner_integral =
      \(events:(V->bool)->bool)
       (mu:(V->bool)->bool#real)
       (zeroH:H) (addH:H->H->H) (negH:H->H)
       (csmul:(real#real)->H->H)
       (innerH:H->H->real#real) (h:V->H).
        if complete_space zeroH addH negH innerH /\
           vector_integrable
             events mu zeroH addH negH innerH h
        then @z:H.
               has_bochner_integral
                 events mu zeroH addH negH csmul innerH h z
        else zeroH in
   let has_real_integral =
      \(events:(V->bool)->bool)
       (mu:(V->bool)->bool#real) (h:V->real) (z:real).
        ?p n:real.
          has_nonnegative_integral events mu
            (\x:V. (abs(h x) + h x) / &2) p /\
          has_nonnegative_integral events mu
            (\x:V. (abs(h x) - h x) / &2) n /\
          z = p - n in
   let real_integral =
      \(events:(V->bool)->bool)
       (mu:(V->bool)->bool#real) (h:V->real).
        if scalar_integrable events mu h
        then @z:real. has_real_integral events mu h z
        else &0 in
   let complex_integrable =
      \(events:(V->bool)->bool)
       (mu:(V->bool)->bool#real) (h:V->real#real).
        scalar_integrable events mu (\x. FST (h x)) /\
        scalar_integrable events mu (\x. SND (h x)) in
   let complex_integral =
      \(events:(V->bool)->bool)
       (mu:(V->bool)->bool#real) (h:V->real#real).
        if complex_integrable events mu h
        then (real_integral events mu (\x. FST (h x)),
              real_integral events mu (\x. SND (h x)))
        else czero in
   let normalized_add_haar_measure =
      \(zeroV:V) (addV:V->V->V) (negV:V->V)
       (innerV:V->V->real)
       (events:(V->bool)->bool)
       (mu:(V->bool)->bool#real).
        (!a:V s:V->bool.
           events s ==> mu (IMAGE (addV a) s) = mu s) /\
        (!R:real.
           ~(FST
             (mu {x:V | vnorm innerV x <= R}))) /\
        has_nonnegative_integral events mu
          (\x:V. exp(--pi * vnorm innerV x pow 2)) (&1) in
   let real_linear =
      \(addV:V->V->V) (smulV:real->V->V)
       (addH:H->H->H) (csmul:(real#real)->H->H)
       (L:V->H).
        (!x y:V. L (addV x y) = addH (L x) (L y)) /\
        (!a:real x:V. L (smulV a x) = csmul (a,&0) (L x)) in
   let has_frechet_derivative =
      \(addV:V->V->V) (smulV:real->V->V)
       (innerV:V->V->real)
       (addH:H->H->H) (negH:H->H)
       (csmul:(real#real)->H->H)
       (innerH:H->H->real#real)
       (f:V->H) (L:V->H) (x:V).
        real_linear addV smulV addH csmul L /\
        (!epsilon:real.
           &0 < epsilon
           ==> ?delta:real.
                 &0 < delta /\
                 !h:V.
                   vnorm innerV h < delta
                   ==> hnorm innerH
                         (addH
                           (addH (f (addV x h)) (negH (f x)))
                           (negH (L h)))
                       <= epsilon * vnorm innerV h) in
   let replace_direction =
      \(u:num->V) (i:num) (v:V) (j:num).
        if j = i then v else u j in
   let extend_direction =
      \(u:num->V) (n:num) (v:V) (i:num).
        if i < n then u i else v in
   let iterated_derivative_family =
      \(addV:V->V->V) (smulV:real->V->V)
       (innerV:V->V->real)
       (addH:H->H->H) (negH:H->H)
       (csmul:(real#real)->H->H)
       (innerH:H->H->real#real)
       (f:V->H) (D:num->V->(num->V)->H).
        (!x:V u:num->V. D 0 x u = f x) /\
        (!n x:V u v:num->V.
           (!i. i < n ==> u i = v i)
           ==> D n x u = D n x v) /\
        (!n x:V u:num->V.
           has_frechet_derivative
             addV smulV innerV addH negH csmul innerH
             (\y:V. D n y u)
             (\h:V. D (SUC n) x (extend_direction u n h))
             x) /\
        (!n x:V u:num->V i:num a b:V.
           i < n
           ==> D n x (replace_direction u i (addV a b)) =
               addH
                 (D n x (replace_direction u i a))
                 (D n x (replace_direction u i b))) /\
        (!n x:V u:num->V i:num r:real a:V.
           i < n
           ==> D n x (replace_direction u i (smulV r a)) =
               csmul (r,&0)
                 (D n x (replace_direction u i a))) in
   let schwartz =
      \(addV:V->V->V) (smulV:real->V->V)
       (innerV:V->V->real)
       (addH:H->H->H) (negH:H->H)
       (csmul:(real#real)->H->H)
       (innerH:H->H->real#real) (f:V->H).
        ?D:num->V->(num->V)->H.
          iterated_derivative_family
            addV smulV innerV addH negH csmul innerH f D /\
          (!n k:num.
             ?C:real.
               &0 <= C /\
               !x:V u:num->V.
                 (!i. i < n ==> vnorm innerV (u i) <= &1)
                 ==> (&1 + vnorm innerV x) pow k *
                     hnorm innerH (D n x u) <= C) in
   let fourier_character =
      \(innerV:V->V->real) (sign:real) (v:V) (w:V).
        (cos(&2 * pi * innerV v w),
         sign * sin(&2 * pi * innerV v w)) in
   let fourier =
      \(events:(V->bool)->bool)
       (mu:(V->bool)->bool#real)
       (zeroH:H) (addH:H->H->H) (negH:H->H)
       (csmul:(real#real)->H->H)
       (innerH:H->H->real#real)
       (innerV:V->V->real) (f:V->H) (v:V).
        bochner_integral
          events mu zeroH addH negH csmul innerH
          (\w:V.
             csmul (fourier_character innerV (-- &1) v w) (f w)) in
   !zeroV:V
    addV:V->V->V
    negV:V->V
    smulV:real->V->V
    innerV:V->V->real
    events:(V->bool)->bool
    mu:(V->bool)->bool#real
    zeroH:H
    addH:H->H->H
    negH:H->H
    csmul:(real#real)->H->H
    innerH:H->H->real#real.
      real_vector_space zeroV addV negV smulV /\
      real_inner_product zeroV addV smulV innerV /\
      finite_dimensional zeroV addV smulV /\
      borel_space addV negV innerV events /\
      measure_space events mu /\
      normalized_add_haar_measure
        zeroV addV negV innerV events mu /\
      complex_vector_space zeroH addH negH csmul /\
      complex_inner_product zeroH addH csmul innerH /\
      complete_space zeroH addH negH innerH
      ==>
      !f g:V->H.
        schwartz
          addV smulV innerV addH negH csmul innerH f /\
        schwartz
          addV smulV innerV addH negH csmul innerH g
        ==>
        complex_integral events mu
          (\xi:V.
             innerH
               (fourier
                 events mu zeroH addH negH csmul innerH innerV f xi)
               (fourier
                 events mu zeroH addH negH csmul innerH innerV g xi)) =
        complex_integral events mu
          (\x:V. innerH (f x) (g x))`;;
