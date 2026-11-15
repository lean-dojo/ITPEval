(*
  Statement-only formalization of Thousand Theorems corpus artifact Q5445112,
  "Fernique's theorem": every Gaussian probability measure on an arbitrary
  complete second-countable real normed vector space admits a positive
  constant for which the exponential of that constant times the squared norm
  is integrable. This file contains no proof.
*)

let q5445112_output = open_out "/dev/null";;
let q5445112_formatter = Format.formatter_of_out_channel q5445112_output;;
let q5445112_previous_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file q5445112_formatter path);;
let q5445112_loaded =
  Toploop.use_file q5445112_formatter "Library/transc.ml";;
Hol_loader.file_loader := q5445112_previous_loader;;
Format.pp_print_flush q5445112_formatter ();;
close_out q5445112_output;;
if not q5445112_loaded then failwith "Unable to load transcendental library";;

let Q5445112_FERNIQUES_THEOREM =
 `let enonnegative =
      \(z:bool#real).
        (FST z /\ SND z = &0) \/
        (~(FST z) /\ &0 <= SND z) in
   let ezero = (F,&0) in
   let eone = (F,&1) in
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
           ==> ?partial:num->bool#real.
                 partial 0 = ezero /\
                 (!n. partial (SUC n) =
                      eadd (partial n) (mu (sets n))) /\
                 esup_sequence partial
                   (mu {x:A | ?n. x IN sets n})) in
   let probability_measure =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real).
        measure_space events mu /\ mu (:A) = eone in
   let normed_real_vector_space =
      \(zero:A) (add:A->A->A) (neg:A->A)
       (smul:real->A->A) (norm:A->real).
        (!x y:A. add x y = add y x) /\
        (!x y z:A. add (add x y) z = add x (add y z)) /\
        (!x:A. add x zero = x) /\
        (!x:A. add x (neg x) = zero) /\
        (!x:A. smul (&1) x = x) /\
        (!a b:real x:A.
           smul (a * b) x = smul a (smul b x)) /\
        (!a b:real x:A.
           smul (a + b) x = add (smul a x) (smul b x)) /\
        (!a:real x y:A.
           smul a (add x y) = add (smul a x) (smul a y)) /\
        (!x:A. &0 <= norm x) /\
        (!x:A. norm x = &0 <=> x = zero) /\
        (!a:real x:A. norm (smul a x) = abs a * norm x) /\
        (!x y:A. norm (add x y) <= norm x + norm y) in
   let vector_tends =
      \(zero:A) (add:A->A->A) (neg:A->A) (norm:A->real)
       (u:num->A) (l:A).
        !epsilon:real.
          &0 < epsilon
          ==> ?N:num. !n:num.
                N <= n
                ==> norm (add (u n) (neg l)) < epsilon in
   let complete_space =
      \(zero:A) (add:A->A->A) (neg:A->A) (norm:A->real).
        !u:num->A.
          (!epsilon:real.
             &0 < epsilon
             ==> ?N:num. !m n:num.
                   N <= m /\ N <= n
                   ==> norm (add (u m) (neg (u n))) < epsilon)
          ==> ?l:A. vector_tends zero add neg norm u l in
   let metric_open =
      \(add:A->A->A) (neg:A->A) (norm:A->real)
       (s:A->bool).
        !x:A.
          x IN s
          ==> ?epsilon:real.
                &0 < epsilon /\
                !y:A.
                  norm (add y (neg x)) < epsilon
                  ==> y IN s in
   let borel_space =
      \(add:A->A->A) (neg:A->A) (norm:A->real)
       (events:(A->bool)->bool).
        sigma_algebra events /\
        (!s:A->bool.
           metric_open add neg norm s ==> events s) /\
        (!other:(A->bool)->bool.
           sigma_algebra other /\
           (!s:A->bool.
              metric_open add neg norm s ==> other s)
           ==> !s:A->bool. events s ==> other s) in
   let second_countable =
      \(add:A->A->A) (neg:A->A) (norm:A->real).
        ?basis:(A->bool)->bool.
          COUNTABLE basis /\
          (!b:A->bool.
             b IN basis ==> metric_open add neg norm b) /\
          (!u:A->bool x:A.
             metric_open add neg norm u /\ x IN u
             ==> ?b:A->bool.
                   b IN basis /\ x IN b /\ b SUBSET u) in
   let scalar_tends =
      \(u:num->real) (l:real).
        !epsilon:real.
          &0 < epsilon
          ==> ?N:num. !n:num.
                N <= n ==> abs(u n - l) < epsilon in
   let almost_everywhere =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real) (P:A->bool).
        ?N:A->bool.
          events N /\
          mu N = ezero /\
          {x:A | ~(P x)} SUBSET N in
   let simple_scalar =
      \(events:(A->bool)->bool) (s:A->real).
        FINITE (IMAGE s (:A)) /\
        (!c:real. events {x:A | s x = c}) in
   let strongly_measurable_scalar =
      \(events:(A->bool)->bool) (h:A->real).
        ?s:num->A->real.
          (!n. simple_scalar events (s n)) /\
          (!x:A. scalar_tends (\n. s n x) (h x)) in
   let ae_strongly_measurable_scalar =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real) (h:A->real).
        ?g:A->real.
          strongly_measurable_scalar events g /\
          almost_everywhere events mu (\x:A. h x = g x) in
   let integrable_simple_scalar =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real) (s:A->real).
        simple_scalar events s /\
        (!c:real.
           c IN IMAGE s (:A) /\ ~(c = &0)
           ==> ~(FST (mu {x:A | s x = c}))) in
   let simple_scalar_integral =
      \(mu:(A->bool)->bool#real) (s:A->real) (z:real).
        ?n:num enum:num->real partial:num->real.
          (!c:real.
             c IN IMAGE s (:A) <=>
             ?i:num. i < n /\ enum i = c) /\
          (!i j:num.
             i < n /\ j < n /\ enum i = enum j ==> i = j) /\
          partial 0 = &0 /\
          (!i:num.
             i < n
             ==> partial (SUC i) =
                 SND (mu {x:A | s x = enum i}) * enum i +
                 partial i) /\
          z = partial n in
   let nonnegative_integral_upper_bound =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real) (h:A->real) (u:real).
        !s:A->real z:real.
          integrable_simple_scalar events mu s /\
          (!x:A. &0 <= s x /\ s x <= h x) /\
          simple_scalar_integral mu s z
          ==> z <= u in
   let has_nonnegative_integral =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real) (h:A->real) (r:real).
        (!x:A. &0 <= h x) /\
        &0 <= r /\
        nonnegative_integral_upper_bound events mu h r /\
        (!u:real.
           &0 <= u /\
           nonnegative_integral_upper_bound events mu h u
           ==> r <= u) in
   let positive_part =
      \(h:A->real) (x:A). (abs(h x) + h x) / &2 in
   let negative_part =
      \(h:A->real) (x:A). (abs(h x) - h x) / &2 in
   let scalar_integrable =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real) (h:A->real).
        ae_strongly_measurable_scalar events mu h /\
        ?p n:real.
          has_nonnegative_integral events mu
            (positive_part h) p /\
          has_nonnegative_integral events mu
            (negative_part h) n in
   let has_real_integral =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real)
       (h:A->real) (z:real).
        ?p n:real.
          has_nonnegative_integral events mu
            (positive_part h) p /\
          has_nonnegative_integral events mu
            (negative_part h) n /\
          z = p - n in
   let real_integral =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real) (h:A->real).
        if scalar_integrable events mu h
        then @z:real. has_real_integral events mu h z
        else &0 in
   let continuous_linear_functional =
      \(add:A->A->A) (smul:real->A->A) (norm:A->real)
       (L:A->real).
        (!x y:A. L (add x y) = L x + L y) /\
        (!a:real x:A. L (smul a x) = a * L x) /\
        (?K:real.
           &0 <= K /\ !x:A. abs(L x) <= K * norm x) in
   let gaussian_measure =
      \(add:A->A->A) (smul:real->A->A) (norm:A->real)
       (events:(A->bool)->bool)
       (mu:(A->bool)->bool#real).
        probability_measure events mu /\
        !L:A->real.
          continuous_linear_functional add smul norm L
          ==> ?m v:real.
                &0 <= v /\
                !t:real.
                  scalar_integrable events mu
                    (\x:A. cos(t * L x)) /\
                  real_integral events mu
                    (\x:A. cos(t * L x)) =
                    exp (--(v * t pow 2) / &2) * cos(t * m) /\
                  scalar_integrable events mu
                    (\x:A. sin(t * L x)) /\
                  real_integral events mu
                    (\x:A. sin(t * L x)) =
                    exp (--(v * t pow 2) / &2) * sin(t * m) in
   !zero:A
    add:A->A->A
    neg:A->A
    smul:real->A->A
    norm:A->real
    events:(A->bool)->bool
    mu:(A->bool)->bool#real.
      normed_real_vector_space zero add neg smul norm /\
      complete_space zero add neg norm /\
      second_countable add neg norm /\
      borel_space add neg norm events /\
      gaussian_measure add smul norm events mu
      ==> ?C:real.
            &0 < C /\
            scalar_integrable events mu
              (\x:A. exp(C * norm x pow 2))`;;
