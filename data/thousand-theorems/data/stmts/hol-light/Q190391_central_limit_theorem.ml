(*
  Statement-only formalization of Thousand Theorems corpus artifact Q190391,
  "Central limit theorem": independent identically distributed real random
  variables with a finite second moment have inverse-square-root normalized
  centered partial sums converging in distribution to a centered Gaussian
  random variable with the same variance, including the zero-variance case.
  This file contains no proof.
*)

let q190391_output = open_out "/dev/null";;
let q190391_formatter = Format.formatter_of_out_channel q190391_output;;
let q190391_previous_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file q190391_formatter path);;
let q190391_loaded =
  Toploop.use_file q190391_formatter "Library/transc.ml";;
Hol_loader.file_loader := q190391_previous_loader;;
Format.pp_print_flush q190391_formatter ();;
close_out q190391_output;;
if not q190391_loaded then failwith "Q190391: failed to load Library/transc.ml";;

let Q190391_CENTRAL_LIMIT_THEOREM = `
  let seq_tends = \a l.
    !e. &0 < e ==> ?N. !n. N <= n ==> abs(a n - l) < e in
  let sigma_space = \events:(A->bool)->bool.
    events UNIV /\
    (!s. events s ==> events (UNIV DIFF s)) /\
    (!s:num->A->bool. (!n. events (s n)) ==>
      events {x | ?n. x IN s n}) in
  let sigma_space' = \events:(B->bool)->bool.
    events UNIV /\
    (!s. events s ==> events (UNIV DIFF s)) /\
    (!s:num->B->bool. (!n. events (s n)) ==>
      events {x | ?n. x IN s n}) in
  let real_open = \u:real->bool.
    !x. x IN u ==> ?d. &0 < d /\
      !y. abs(y - x) < d ==> y IN u in
  let sigma_real = \events:(real->bool)->bool.
    events UNIV /\
    (!s. events s ==> events (UNIV DIFF s)) /\
    (!s:num->real->bool. (!n. events (s n)) ==>
      events {x | ?n. x IN s n}) in
  let real_events = \s:real->bool.
    !events. sigma_real events /\
      (!u. real_open u ==> events u) ==> events s in
  let probability = \events:(A->bool)->bool p.
    sigma_space events /\
    p UNIV = &1 /\
    (!s. events s ==> &0 <= p s) /\
    (!s:num->A->bool.
      (!n. events (s n)) /\
      (!i j. ~(i = j) ==> DISJOINT (s i) (s j))
      ==> seq_tends
            (\n. sum (0..n) (\k. p (s k)))
            (p {x | ?k. x IN s k})) in
  let probability' = \events:(B->bool)->bool p.
    sigma_space' events /\
    p UNIV = &1 /\
    (!s. events s ==> &0 <= p s) /\
    (!s:num->B->bool.
      (!n. events (s n)) /\
      (!i j. ~(i = j) ==> DISJOINT (s i) (s j))
      ==> seq_tends
            (\n. sum (0..n) (\k. p (s k)))
            (p {x | ?k. x IN s k})) in
  let probability_real = \p:(real->bool)->real.
    sigma_real real_events /\
    p UNIV = &1 /\
    (!s. real_events s ==> &0 <= p s) /\
    (!s:num->real->bool.
      (!n. real_events (s n)) /\
      (!i j. ~(i = j) ==> DISJOINT (s i) (s j))
      ==> seq_tends
            (\n. sum (0..n) (\k. p (s k)))
            (p {x | ?k. x IN s k})) in
  let measurable = \events:(A->bool)->bool f:A->real.
    !s. real_events s ==> events {x | f x IN s} in
  let measurable' = \events:(B->bool)->bool f:B->real.
    !s. real_events s ==> events {x | f x IN s} in
  let ae_equal = \events:(A->bool)->bool p f g.
    ?n. events n /\ p n = &0 /\
      !x. ~(x IN n) ==> f x = g x in
  let ae_equal' = \events:(B->bool)->bool p f g.
    ?n. events n /\ p n = &0 /\
      !x. ~(x IN n) ==> f x = g x in
  let map_law = \events:(A->bool)->bool p f law.
    probability_real law /\
    ?g. measurable events g /\ ae_equal events p f g /\
      !s. real_events s ==> law s = p {x | g x IN s} in
  let map_law' = \events:(B->bool)->bool p f law.
    probability_real law /\
    ?g. measurable' events g /\ ae_equal' events p f g /\
      !s. real_events s ==> law s = p {x | g x IN s} in
  let simple_scalar = \s:real->real.
    FINITE (IMAGE s UNIV) /\
    !c. real_events {x | s x = c} in
  let integrable_simple_scalar =
      \law:(real->bool)->real s:real->real.
    simple_scalar s /\
    !x. &0 <= s x in
  let simple_scalar_integral =
      \law:(real->bool)->real s:real->real.
    @z. ?values.
      FINITE values /\
      IMAGE s UNIV SUBSET values /\
      z = sum values (\c. c * law {x | s x = c}) in
  let nonnegative_integral_upper_bound =
      \law:(real->bool)->real h:real->real b.
    !s. integrable_simple_scalar law s /\
      (!x. s x <= h x)
      ==> simple_scalar_integral law s <= b in
  let has_nonnegative_integral =
      \law:(real->bool)->real h:real->real i.
    (!x. &0 <= h x) /\
    nonnegative_integral_upper_bound law h i /\
    !b. nonnegative_integral_upper_bound law h b ==> i <= b in
  let strongly_measurable_scalar = \h:real->real.
    ?s:num->real->real.
      (!n. simple_scalar (s n)) /\
      !x. seq_tends (\n. s n x) (h x) in
  let almost_everywhere =
      \law:(real->bool)->real predicate:real->bool.
    ?n. real_events n /\ law n = &0 /\
      {x | ~(predicate x)} SUBSET n in
  let ae_strongly_measurable =
      \law:(real->bool)->real h:real->real.
    ?g. strongly_measurable_scalar g /\
      almost_everywhere law (\x. h x = g x) in
  let positive_part = \x. max x (&0) in
  let negative_part = \x. max (--x) (&0) in
  let scalar_integrable = \law:(real->bool)->real h:real->real.
    ae_strongly_measurable law h /\
    (?ip. has_nonnegative_integral law (\x. positive_part (h x)) ip) /\
    (?ineg. has_nonnegative_integral law (\x. negative_part (h x)) ineg) in
  let has_real_integral =
      \law:(real->bool)->real h:real->real i.
    ?ip ineg.
      has_nonnegative_integral law (\x. positive_part (h x)) ip /\
      has_nonnegative_integral law (\x. negative_part (h x)) ineg /\
      i = ip - ineg in
  let real_integral = \law:(real->bool)->real h:real->real.
    if scalar_integrable law h
    then @i. has_real_integral law h i
    else &0 in
  let l2_law = \law:(real->bool)->real.
    scalar_integrable law (\x. x) /\
    scalar_integrable law (\x. x pow 2) /\
    (let m = real_integral law (\x. x) in
     scalar_integrable law (\x. (x - m) pow 2)) in
  let mem_l2 = \events:(A->bool)->bool p f:A->real.
    ?law. map_law events p f law /\ l2_law law in
  let ident_distrib = \events:(A->bool)->bool p f g.
    ?law. map_law events p f law /\ map_law events p g law in
  let independent_sequence =
      \events:(A->bool)->bool p X:num->A->real.
    ?V:num->A->real.
      (!i. measurable events (V i) /\ ae_equal events p (X i) (V i)) /\
      !inds sets.
        FINITE (inds:num->bool) /\
        (!i. i IN inds ==> real_events (sets i))
        ==> p (INTERS (IMAGE (\i. {x | V i x IN sets i}) inds)) =
            product inds (\i. p {x | V i x IN sets i}) in
  let continuous_real = \h:real->real.
    !x e. &0 < e ==> ?d. &0 < d /\
      !y. abs(y - x) < d ==> abs(h y - h x) < e in
  let bounded_continuous = \h:real->real.
    continuous_real h /\ ?c. !x. abs(h x) <= c in
  let weak_tends =
      \laws:num->(real->bool)->real limit:(real->bool)->real.
    (!n. probability_real (laws n)) /\
    probability_real limit /\
    !h. bounded_continuous h ==>
      seq_tends
        (\n. real_integral (laws n) h)
        (real_integral limit h) in
  let centered_gaussian = \law:(real->bool)->real variance.
    probability_real law /\
    &0 <= variance /\
    !t.
      real_integral law (\x. cos(t * x)) =
        exp (--(variance * t pow 2) / &2) /\
      real_integral law (\x. sin(t * x)) = &0 in
  let has_centered_gaussian_law =
      \events:(B->bool)->bool p Y:B->real variance.
    ?law. map_law' events p Y law /\ centered_gaussian law variance in
  let tends_in_distribution =
      \events:(A->bool)->bool p f:num->A->real
       events':(B->bool)->bool p' Y:B->real.
    ?laws limit.
      (!n. map_law events p (f n) (laws n)) /\
      map_law' events' p' Y limit /\
      weak_tends laws limit in
  !events:(A->bool)->bool p:(A->bool)->real
   events':(B->bool)->bool p':(B->bool)->real
   X:num->A->real Y:B->real.
    probability events p /\ probability' events' p'
    ==>
    let law0 = @law. map_law events p (X 0) law /\ l2_law law in
    let mean = real_integral law0 (\x. x) in
    let variance = real_integral law0 (\x. (x - mean) pow 2) in
    has_centered_gaussian_law events' p' Y variance /\
    mem_l2 events p (X 0) /\
    independent_sequence events p X /\
    (!i. ident_distrib events p (X i) (X 0))
    ==>
    tends_in_distribution
      events p
      (\n x.
        inv(sqrt(&n)) *
        (sum {k | k < n} (\k. X k x) - &n * mean))
      events' p' Y
`;;
