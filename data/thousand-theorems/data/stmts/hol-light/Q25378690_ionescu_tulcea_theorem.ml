(*
  Statement-only formalization of Thousand Theorems corpus artifact Q25378690,
  "Ionescu-Tulcea theorem": a measurable family of Markov kernels on
  successively typed finite trajectories extends to a probability kernel on
  infinite trajectories with the prescribed prefix and transition laws. This
  file contains no proof.
*)

let Q25378690_IONESCU_TULCEA_THEOREM =
 `let seq_tends =
      \(u:num->real) (l:real).
        !e. &0 < e ==> ?N. !n. N <= n ==> abs(u n - l) < e in
   let sigma_algebra =
      \(carrier:A->bool) (events:(A->bool)->bool).
        (!s:A->bool. s IN events ==> s SUBSET carrier) /\
        {} IN events /\
        carrier IN events /\
        (!s:A->bool.
           s IN events ==> carrier DIFF s IN events) /\
        (!sets:num->A->bool.
           (!n. sets n IN events)
           ==> {x:A | ?n. x IN sets n} IN events) in
   let history_sigma_algebra =
      \(carrier:(num->A)->bool)
       (events:((num->A)->bool)->bool).
        (!s:(num->A)->bool. s IN events ==> s SUBSET carrier) /\
        {} IN events /\
        carrier IN events /\
        (!s:(num->A)->bool.
           s IN events ==> carrier DIFF s IN events) /\
        (!sets:num->(num->A)->bool.
           (!n. sets n IN events)
           ==> {x:num->A | ?n. x IN sets n} IN events) in
   let generated_history_events =
      \(carrier:(num->A)->bool)
       (generators:((num->A)->bool)->bool)
       (s:(num->A)->bool).
        !events:((num->A)->bool)->bool.
          history_sigma_algebra carrier events /\
          (!g:(num->A)->bool. g IN generators ==> g IN events)
          ==> s IN events in
   let typed_prefix =
      \(states:num->A->bool) (n:num) (h:num->A).
        !i. i <= n ==> h i IN states i in
   let typed_path =
      \(states:num->A->bool) (x:num->A).
        !i. x i IN states i in
   let prefix_carrier =
      \(states:num->A->bool) (n:num).
        {h:num->A | typed_prefix states n h} in
   let path_carrier =
      \(states:num->A->bool).
        {x:num->A | typed_path states x} in
   let prefix_generators =
      \(states:num->A->bool)
       (state_events:num->(A->bool)->bool)
       (n:num).
        {c:(num->A)->bool |
          ?i u.
            i <= n /\
            u IN state_events i /\
            c = {h:num->A |
                   typed_prefix states n h /\ h i IN u}} in
   let path_generators =
      \(states:num->A->bool)
       (state_events:num->(A->bool)->bool).
        {c:(num->A)->bool |
          ?i u.
            u IN state_events i /\
            c = {x:num->A |
                   typed_path states x /\ x i IN u}} in
   let prefix_events =
      \(states:num->A->bool)
       (state_events:num->(A->bool)->bool)
       (n:num).
        generated_history_events
          (prefix_carrier states n)
          (prefix_generators states state_events n) in
   let path_events =
      \(states:num->A->bool)
       (state_events:num->(A->bool)->bool).
        generated_history_events
          (path_carrier states)
          (path_generators states state_events) in
   let state_probability_measure =
      \(carrier:A->bool)
       (events:(A->bool)->bool)
       (mu:(A->bool)->real).
        (!s:A->bool. s IN events ==> s SUBSET carrier) /\
        {} IN events /\
        carrier IN events /\
        (!s:A->bool.
           s IN events ==> carrier DIFF s IN events) /\
        (!sets:num->A->bool.
           (!n. sets n IN events)
           ==> {x:A | ?n. x IN sets n} IN events) /\
        mu {} = &0 /\
        mu carrier = &1 /\
        (!s:A->bool. s IN events ==> &0 <= mu s) /\
        (!sets:num->A->bool.
           (!n. sets n IN events) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> seq_tends
                 (\N. sum {k:num | k < N} (\k. mu (sets k)))
                 (mu {x:A | ?k. x IN sets k})) in
   let path_probability_measure =
      \(carrier:(num->A)->bool)
       (events:((num->A)->bool)->bool)
       (mu:((num->A)->bool)->real).
        (!s:(num->A)->bool. s IN events ==> s SUBSET carrier) /\
        {} IN events /\
        carrier IN events /\
        (!s:(num->A)->bool.
           s IN events ==> carrier DIFF s IN events) /\
        (!sets:num->(num->A)->bool.
           (!n. sets n IN events)
           ==> {x:num->A | ?n. x IN sets n} IN events) /\
        mu {} = &0 /\
        mu carrier = &1 /\
        (!s:(num->A)->bool. s IN events ==> &0 <= mu s) /\
        (!sets:num->(num->A)->bool.
           (!n. sets n IN events) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> seq_tends
                 (\N. sum {k:num | k < N} (\k. mu (sets k)))
                 (mu {x:num->A | ?k. x IN sets k})) in
   let history_measurable_real =
      \(carrier:(num->A)->bool)
       (events:((num->A)->bool)->bool)
       (f:(num->A)->real).
        !r. {x:num->A | x IN carrier /\ f x <= r} IN events in
   let unit_interval_integral =
      \(carrier:(num->A)->bool)
       (events:((num->A)->bool)->bool)
       (mu:((num->A)->bool)->real)
       (f:(num->A)->real)
       (z:real).
        history_measurable_real carrier events f /\
        (!x:num->A. x IN carrier ==> &0 <= f x /\ f x <= &1) /\
        seq_tends
          (\m. inv(&(2 EXP m)) *
               sum {k:num | 1 <= k /\ k <= 2 EXP m}
                 (\k. mu {x:num->A |
                            x IN carrier /\
                            &k / &(2 EXP m) <= f x}))
          z in
   let markov_kernel_family =
      \(states:num->A->bool)
       (state_events:num->(A->bool)->bool)
       (kernel:num->(num->A)->(A->bool)->real).
        (!n. sigma_algebra (states n) (state_events n)) /\
        (!m n x:A.
           x IN states m /\ x IN states n ==> m = n) /\
        (!n h:num->A.
           typed_prefix states n h
           ==> state_probability_measure
                 (states (SUC n))
                 (state_events (SUC n))
                 (kernel n h)) /\
        (!n u.
           u IN state_events (SUC n)
           ==> history_measurable_real
                 (prefix_carrier states n)
                 (prefix_events states state_events n)
                 (\h:num->A. kernel n h u)) /\
        (!n h g:num->A.
           typed_prefix states n h /\
           typed_prefix states n g /\
           (!i. i <= n ==> h i = g i)
           ==> !u:A->bool. kernel n h u = kernel n g u) in
   let trajectory_kernel =
      \(states:num->A->bool)
       (state_events:num->(A->bool)->bool)
       (kernel:num->(num->A)->(A->bool)->real)
       (a:num)
       (eta:(num->A)->((num->A)->bool)->real).
        (!h:num->A.
           typed_prefix states a h
           ==> path_probability_measure
                 (path_carrier states)
                 (path_events states state_events)
                 (eta h)) /\
        (!w:(num->A)->bool.
           w IN path_events states state_events
           ==> history_measurable_real
                 (prefix_carrier states a)
                 (prefix_events states state_events a)
                 (\h:num->A. eta h w)) /\
        (!h g:num->A.
           typed_prefix states a h /\
           typed_prefix states a g /\
           (!i. i <= a ==> h i = g i)
           ==> !w:(num->A)->bool. eta h w = eta g w) /\
        (!h:num->A.
           typed_prefix states a h
           ==> !c:(num->A)->bool.
                 c IN prefix_events states state_events a
                 ==> eta h
                       {x:num->A |
                          typed_path states x /\ x IN c} =
                     (if h IN c then &1 else &0)) /\
        (!h:num->A.
           typed_prefix states a h
           ==> !n c u.
                 a <= n /\
                 c IN prefix_events states state_events n /\
                 u IN state_events (SUC n)
                 ==> unit_interval_integral
                       (path_carrier states)
                       (path_events states state_events)
                       (eta h)
                       (\x:num->A.
                          if x IN c then kernel n x u else &0)
                       (eta h
                         {x:num->A |
                            typed_path states x /\
                            x IN c /\
                            x (SUC n) IN u})) in
   !states:num->A->bool
    state_events:num->(A->bool)->bool
    kernel:num->(num->A)->(A->bool)->real.
      markov_kernel_family states state_events kernel
      ==> ?traj:num->(num->A)->((num->A)->bool)->real.
            !a. trajectory_kernel
                  states state_events kernel a (traj a)`;;
