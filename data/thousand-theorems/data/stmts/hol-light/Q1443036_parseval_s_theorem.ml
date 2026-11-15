(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1443036,
  "Parseval's theorem": for a complex L2 function on an additive circle of
  arbitrary positive circumference, the sum over all integer Fourier modes of
  the squared coefficient norms equals its normalized Haar L2 energy. This
  file contains no proof.
*)

let q1443036_output = open_out "/dev/null";;
let q1443036_formatter = Format.formatter_of_out_channel q1443036_output;;
let q1443036_previous_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file q1443036_formatter path);;
let q1443036_loaded =
  Toploop.use_file q1443036_formatter "Library/transc.ml";;
Hol_loader.file_loader := q1443036_previous_loader;;
Format.pp_print_flush q1443036_formatter ();;
close_out q1443036_output;;
if not q1443036_loaded then failwith "Unable to load transcendental library";;

let Q1443036_PARSEVAL_S_THEOREM =
 `let czero = (&0,&0) in
  let cadd =
    \(z:real#real) (w:real#real).
      (FST z + FST w,SND z + SND w) in
  let cneg =
    \(z:real#real). (--(FST z),--(SND z)) in
  let cmul =
    \(z:real#real) (w:real#real).
      (FST z * FST w - SND z * SND w,
       FST z * SND w + SND z * FST w) in
  let cscale =
    \(a:real) (z:real#real). (a * FST z,a * SND z) in
  let cmod2 =
    \(z:real#real). FST z pow 2 + SND z pow 2 in
  let cdist =
    \(z:real#real) (w:real#real).
      sqrt(cmod2 (cadd z (cneg w))) in
  let circle_carrier =
    \(period:real) (x:real). &0 <= x /\ x < period in
  let sigma_algebra =
    \(carrier:real->bool) (events:(real->bool)->bool).
      events {} /\
      events carrier /\
      (!s:real->bool. events s ==> s SUBSET carrier) /\
      (!s:real->bool.
         events s ==> events (carrier DIFF s)) /\
      (!sets:num->real->bool.
         (!n. events (sets n))
         ==> events {x:real | ?n. x IN sets n}) in
  let measure_space =
    \(carrier:real->bool) (events:(real->bool)->bool)
     (mu:(real->bool)->real).
      sigma_algebra carrier events /\
      (!s:real->bool. events s ==> &0 <= mu s) /\
      mu {} = &0 /\
      (!sets:num->real->bool.
         (!n. events (sets n)) /\
         (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
         ==> (\n. mu (sets n)) sums
             (mu {x:real | ?n. x IN sets n})) in
  let relatively_open =
    \(carrier:real->bool) (s:real->bool).
      s SUBSET carrier /\
      !x:real.
        x IN s
        ==> ?epsilon:real.
              &0 < epsilon /\
              !y:real.
                y IN carrier /\ abs(y - x) < epsilon
                ==> y IN s in
  let borel_space =
    \(carrier:real->bool) (events:(real->bool)->bool).
      sigma_algebra carrier events /\
      (!s:real->bool.
         relatively_open carrier s ==> events s) /\
      (!other:(real->bool)->bool.
         sigma_algebra carrier other /\
         (!s:real->bool.
            relatively_open carrier s ==> other s)
         ==> !s:real->bool. events s ==> other s) in
  let normalized_circle_measure =
    \(period:real) (events:(real->bool)->bool)
     (mu:(real->bool)->real).
      let carrier = circle_carrier period in
      borel_space carrier events /\
      measure_space carrier events mu /\
      mu carrier = &1 /\
      (!a b:real.
         &0 <= a /\ a <= b /\ b <= period
         ==> mu {x:real |
                  x IN carrier /\ a <= x /\ x < b} =
             (b - a) / period) in
  let almost_everywhere =
    \(carrier:real->bool) (events:(real->bool)->bool)
     (mu:(real->bool)->real) (P:real->bool).
      ?N:real->bool.
        events N /\
        mu N = &0 /\
        {x:real | x IN carrier /\ ~(P x)} SUBSET N in
  let scalar_tends =
    \(u:num->real) (l:real).
      !epsilon:real.
        &0 < epsilon
        ==> ?N:num. !n:num.
              N <= n ==> abs(u n - l) < epsilon in
  let complex_tends =
    \(u:num->real#real) (l:real#real).
      !epsilon:real.
        &0 < epsilon
        ==> ?N:num. !n:num.
              N <= n ==> cdist (u n) l < epsilon in
  let simple_scalar =
    \(carrier:real->bool) (events:(real->bool)->bool)
     (s:real->real).
      FINITE (IMAGE s carrier) /\
      (!c:real.
         events {x:real | x IN carrier /\ s x = c}) in
  let simple_complex =
    \(carrier:real->bool) (events:(real->bool)->bool)
     (s:real->real#real).
      FINITE (IMAGE s carrier) /\
      (!c:real#real.
         events {x:real | x IN carrier /\ s x = c}) in
  let strongly_measurable_scalar =
    \(carrier:real->bool) (events:(real->bool)->bool)
     (h:real->real).
      ?s:num->real->real.
        (!n. simple_scalar carrier events (s n)) /\
        (!x:real.
           x IN carrier
           ==> scalar_tends (\n. s n x) (h x)) in
  let strongly_measurable_complex =
    \(carrier:real->bool) (events:(real->bool)->bool)
     (h:real->real#real).
      ?s:num->real->real#real.
        (!n. simple_complex carrier events (s n)) /\
        (!x:real.
           x IN carrier
           ==> complex_tends (\n. s n x) (h x)) in
  let ae_strongly_measurable_scalar =
    \(carrier:real->bool) (events:(real->bool)->bool)
     (mu:(real->bool)->real) (h:real->real).
      ?g:real->real.
        strongly_measurable_scalar carrier events g /\
        almost_everywhere carrier events mu
          (\x. h x = g x) in
  let ae_strongly_measurable_complex =
    \(carrier:real->bool) (events:(real->bool)->bool)
     (mu:(real->bool)->real) (h:real->real#real).
      ?g:real->real#real.
        strongly_measurable_complex carrier events g /\
        almost_everywhere carrier events mu
          (\x. h x = g x) in
  let simple_scalar_integral =
    \(carrier:real->bool) (mu:(real->bool)->real)
     (s:real->real) (z:real).
      ?n:num enum:num->real partial:num->real.
        (!c:real.
           c IN IMAGE s carrier <=>
           ?i:num. i < n /\ enum i = c) /\
        (!i j:num.
           i < n /\ j < n /\ enum i = enum j ==> i = j) /\
        partial 0 = &0 /\
        (!i:num.
           i < n
           ==> partial (SUC i) =
               mu {x:real |
                    x IN carrier /\ s x = enum i} *
               enum i + partial i) /\
        z = partial n in
  let simple_complex_integral =
    \(carrier:real->bool) (mu:(real->bool)->real)
     (s:real->real#real) (z:real#real).
      ?n:num enum:num->real#real partial:num->real#real.
        (!c:real#real.
           c IN IMAGE s carrier <=>
           ?i:num. i < n /\ enum i = c) /\
        (!i j:num.
           i < n /\ j < n /\ enum i = enum j ==> i = j) /\
        partial 0 = czero /\
        (!i:num.
           i < n
           ==> partial (SUC i) =
               cadd
                 (cscale
                   (mu {x:real |
                          x IN carrier /\ s x = enum i})
                   (enum i))
                 (partial i)) /\
        z = partial n in
  let nonnegative_integral_upper_bound =
    \(carrier:real->bool) (events:(real->bool)->bool)
     (mu:(real->bool)->real) (h:real->real) (u:real).
      !s:real->real z:real.
        simple_scalar carrier events s /\
        (!x:real.
           x IN carrier ==> &0 <= s x /\ s x <= h x) /\
        simple_scalar_integral carrier mu s z
        ==> z <= u in
  let has_nonnegative_integral =
    \(carrier:real->bool) (events:(real->bool)->bool)
     (mu:(real->bool)->real) (h:real->real) (r:real).
      (!x:real. x IN carrier ==> &0 <= h x) /\
      &0 <= r /\
      nonnegative_integral_upper_bound
        carrier events mu h r /\
      (!u:real.
         &0 <= u /\
         nonnegative_integral_upper_bound
           carrier events mu h u
         ==> r <= u) in
  let nonnegative_integral =
    \(carrier:real->bool) (events:(real->bool)->bool)
     (mu:(real->bool)->real) (h:real->real).
      if ?r:real.
           has_nonnegative_integral carrier events mu h r
      then @r:real.
             has_nonnegative_integral carrier events mu h r
      else &0 in
  let scalar_integrable =
    \(carrier:real->bool) (events:(real->bool)->bool)
     (mu:(real->bool)->real) (h:real->real).
      ae_strongly_measurable_scalar carrier events mu h /\
      (?r:real.
         has_nonnegative_integral carrier events mu
           (\x. abs(h x)) r) in
  let has_real_integral =
    \(carrier:real->bool) (events:(real->bool)->bool)
     (mu:(real->bool)->real) (h:real->real) (z:real).
      ?p n:real.
        has_nonnegative_integral carrier events mu
          (\x. (abs(h x) + h x) / &2) p /\
        has_nonnegative_integral carrier events mu
          (\x. (abs(h x) - h x) / &2) n /\
        z = p - n in
  let real_integral =
    \(carrier:real->bool) (events:(real->bool)->bool)
     (mu:(real->bool)->real) (h:real->real).
      if scalar_integrable carrier events mu h
      then @z:real.
             has_real_integral carrier events mu h z
      else &0 in
  let complex_integrable =
    \(carrier:real->bool) (events:(real->bool)->bool)
     (mu:(real->bool)->real) (h:real->real#real).
      scalar_integrable carrier events mu
        (\x. FST (h x)) /\
      scalar_integrable carrier events mu
        (\x. SND (h x)) in
  let complex_integral =
    \(carrier:real->bool) (events:(real->bool)->bool)
     (mu:(real->bool)->real) (h:real->real#real).
      if complex_integrable carrier events mu h
      then (real_integral carrier events mu
              (\x. FST (h x)),
            real_integral carrier events mu
              (\x. SND (h x)))
      else czero in
  let l2_function =
    \(carrier:real->bool) (events:(real->bool)->bool)
     (mu:(real->bool)->real) (f:real->real#real).
      ae_strongly_measurable_complex carrier events mu f /\
      (?r:real.
         has_nonnegative_integral carrier events mu
           (\x. cmod2 (f x)) r) in
  let integer_frequency =
    \n:num.
      if EVEN n
      then &(n DIV 2)
      else --(&(n DIV 2 + 1)) in
  let fourier_character =
    \(period:real) (n:num) (x:real).
      let theta =
        &2 * pi * integer_frequency n * x / period in
      (cos theta,--(sin theta)) in
  let fourier_coefficient =
    \(period:real) (carrier:real->bool)
     (events:(real->bool)->bool)
     (mu:(real->bool)->real)
     (f:real->real#real) (n:num).
      complex_integral carrier events mu
        (\x. cmul (fourier_character period n x) (f x)) in
  !period:real.
    &0 < period
    ==> let carrier = circle_carrier period in
        !events:(real->bool)->bool
         mu:(real->bool)->real.
          normalized_circle_measure period events mu
          ==> !f:real->real#real.
                l2_function carrier events mu f
                ==> infsum (:num)
                      (\n. cmod2
                        (fourier_coefficient
                          period carrier events mu f n)) =
                    nonnegative_integral carrier events mu
                      (\x. cmod2 (f x))`;;
