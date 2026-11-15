(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1966978,
  "Lévy continuity theorem": weak convergence of probability measures on a
  finite-dimensional real inner-product space is equivalent to pointwise
  convergence of their characteristic functions. This file contains no proof.
*)

let q1966978_output = open_out "/dev/null";;
let q1966978_formatter = Format.formatter_of_out_channel q1966978_output;;
let q1966978_previous_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file q1966978_formatter path);;
let q1966978_loaded =
  Toploop.use_file q1966978_formatter "Library/transc.ml";;
Hol_loader.file_loader := q1966978_previous_loader;;
Format.pp_print_flush q1966978_formatter ();;
close_out q1966978_output;;
if not q1966978_loaded then
  failwith "Q1966978: failed to load Library/transc.ml";;

let Q1966978_LEVY_CONTINUITY_THEOREM = `
  let seq_tends = \(u:num->real) (z:real).
    !epsilon:real.
      &0 < epsilon
      ==> ?N:num. !n:num. N <= n ==> abs(u n - z) < epsilon in
  let complex_seq_tends = \(u:num->real#real) (z:real#real).
    seq_tends (\n. FST(u n)) (FST z) /\
    seq_tends (\n. SND(u n)) (SND z) in
  let real_inner_product_space =
      \(zero:E) (add:E->E->E) (neg:E->E)
       (smul:real->E->E) (inner:E->E->real) (norm:E->real).
    (!x y:E. add x y = add y x) /\
    (!x y z:E. add (add x y) z = add x (add y z)) /\
    (!x:E. add x zero = x) /\
    (!x:E. add x (neg x) = zero) /\
    (!x:E. smul (&1) x = x) /\
    (!a b:real. !x:E. smul (a * b) x = smul a (smul b x)) /\
    (!a b:real. !x:E. smul (a + b) x = add (smul a x) (smul b x)) /\
    (!a:real. !x y:E. smul a (add x y) = add (smul a x) (smul a y)) /\
    (!x y:E. inner x y = inner y x) /\
    (!x y z:E. inner (add x y) z = inner x z + inner y z) /\
    (!a:real. !x y:E. inner (smul a x) y = a * inner x y) /\
    (!x:E. &0 <= inner x x) /\
    (!x:E. inner x x = &0 <=> x = zero) /\
    (!x:E. norm x = sqrt(inner x x)) in
  let finite_dimensional =
      \(zero:E) (add:E->E->E) (smul:real->E->E).
    ?d:num basis:num->E.
      !x:E.
        ?coeff:num->real partial:num->E.
          partial 0 = zero /\
          (!i:num.
             i < d
             ==> partial (SUC i) =
                 add (partial i) (smul (coeff i) (basis i))) /\
          partial d = x in
  let open_set = \(add:E->E->E) (neg:E->E) (norm:E->real)
                   (u:E->bool).
    !x:E.
      x IN u
      ==> ?epsilon:real.
            &0 < epsilon /\
            !y:E. norm (add y (neg x)) < epsilon ==> y IN u in
  let sigma_algebra = \(events:(E->bool)->bool).
    events (:E) /\
    (!s:E->bool. events s ==> events ((:E) DIFF s)) /\
    (!sets:num->E->bool.
       (!n:num. events (sets n))
       ==> events {x:E | ?n:num. x IN sets n}) in
  let borel_event = \(add:E->E->E) (neg:E->E) (norm:E->real)
                     (s:E->bool).
    !events:(E->bool)->bool.
      sigma_algebra events /\
      (!u:E->bool. open_set add neg norm u ==> events u)
      ==> events s in
  let borel_space = \(add:E->E->E) (neg:E->E) (norm:E->real)
                     (events:(E->bool)->bool).
    !s:E->bool. events s <=> borel_event add neg norm s in
  let probability = \(events:(E->bool)->bool)
                     (mu:(E->bool)->real).
    sigma_algebra events /\
    mu {} = &0 /\
    mu (:E) = &1 /\
    (!s:E->bool. events s ==> &0 <= mu s) /\
    (!sets:num->E->bool.
       (!n:num. events (sets n)) /\
       (!i j:num. ~(i = j) ==> DISJOINT (sets i) (sets j))
       ==> seq_tends
             (\N:num. sum {k:num | k < N} (\k. mu (sets k)))
             (mu {x:E | ?k:num. x IN sets k})) in
  let continuous = \(add:E->E->E) (neg:E->E) (norm:E->real)
                    (h:E->real).
    !x:E epsilon:real.
      &0 < epsilon
      ==> ?delta:real.
            &0 < delta /\
            !y:E.
              norm (add y (neg x)) < delta
              ==> abs(h y - h x) < epsilon in
  let bounded_continuous =
      \(add:E->E->E) (neg:E->E) (norm:E->real) (h:E->real).
    continuous add neg norm h /\
    ?bound:real. !x:E. abs(h x) <= bound in
  let simple_function = \(events:(E->bool)->bool) (s:E->real).
    (!x:E. &0 <= s x) /\
    FINITE (IMAGE s (:E)) /\
    (!c:real. events {x:E | s x = c}) in
  let simple_integral = \(mu:(E->bool)->real) (s:E->real).
    sum (IMAGE s (:E)) (\c:real. c * mu {x:E | s x = c}) in
  let lintegral_upper =
      \(events:(E->bool)->bool) (mu:(E->bool)->real)
       (h:E->real) (upper:real).
    !s:E->real.
      simple_function events s /\
      (!x:E. s x <= h x)
      ==> simple_integral mu s <= upper in
  let has_lintegral =
      \(events:(E->bool)->bool) (mu:(E->bool)->real)
       (h:E->real) (z:real).
    &0 <= z /\
    lintegral_upper events mu h z /\
    (!upper:real.
       &0 <= upper /\
       lintegral_upper events mu h upper
       ==> z <= upper) in
  let lintegral =
      \(events:(E->bool)->bool) (mu:(E->bool)->real) (h:E->real).
    @z:real. has_lintegral events mu h z in
  let integral =
      \(events:(E->bool)->bool) (mu:(E->bool)->real) (h:E->real).
    lintegral events mu (\x:E. if &0 <= h x then h x else &0) -
    lintegral events mu (\x:E. if h x < &0 then --(h x) else &0) in
  let weak_tends =
      \(add:E->E->E) (neg:E->E) (norm:E->real)
       (events:(E->bool)->bool)
       (mu:num->(E->bool)->real) (mu0:(E->bool)->real).
    !h:E->real.
      bounded_continuous add neg norm h
      ==> seq_tends
            (\n:num. integral events (mu n) h)
            (integral events mu0 h) in
  let char_fun =
      \(events:(E->bool)->bool) (inner:E->E->real)
       (mu:(E->bool)->real) (t:E).
    (integral events mu (\x:E. cos(inner t x)),
     integral events mu (\x:E. sin(inner t x))) in
  !zero:E
   add:E->E->E
   neg:E->E
   smul:real->E->E
   inner:E->E->real
   norm:E->real
   events:(E->bool)->bool
   mu:num->(E->bool)->real
   mu0:(E->bool)->real.
    real_inner_product_space zero add neg smul inner norm /\
    finite_dimensional zero add smul /\
    borel_space add neg norm events /\
    (!n:num. probability events (mu n)) /\
    probability events mu0
    ==>
    (weak_tends add neg norm events mu mu0 <=>
     !t:E.
       complex_seq_tends
         (\n:num. char_fun events inner (mu n) t)
         (char_fun events inner mu0 t))
`;;
