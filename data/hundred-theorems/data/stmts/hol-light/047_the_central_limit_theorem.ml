(*
  Statement-only formalization of "The Central Limit Theorem" from Hundred
  Theorems artifact 047 (hundred-theorems__hol-light__047). It states the
  zero-mean and centered central limit theorems for identically distributed
  independent real random variables on an arbitrary probability space:
  normalized partial sums converge weakly to the standard normal law. This
  file contains no proof.
*)

let HUNDRED_THEOREMS_047_CENTRAL_LIMIT_THEOREM_ZERO_MEAN =
 `let seq_tends =
      \(u:num->real) l.
        !e. &0 < e ==> ?N. !n. N <= n ==> abs(u n - l) < e in
   let probability_space =
      \(carrier:A->bool) (events:(A->bool)->bool)
       (p:(A->bool)->real).
        (!s. s IN events ==> s SUBSET carrier) /\
        {} IN events /\
        carrier IN events /\
        (!s. s IN events ==> carrier DIFF s IN events) /\
        (!sets:num->A->bool.
           (!n. sets n IN events)
           ==> {a:A | ?n. a IN sets n} IN events) /\
        p {} = &0 /\
        p carrier = &1 /\
        (!s. s IN events ==> &0 <= p s) /\
        (!sets:num->A->bool.
           (!n. sets n IN events) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> seq_tends
                 (\n. sum {k:num | k < n} (\k. p (sets k)))
                 (p {a:A | ?k. a IN sets k})) in
   let random_variable =
      \(carrier:A->bool) (events:(A->bool)->bool) (Y:A->real).
        !x. {a:A | a IN carrier /\ Y a <= x} IN events in
   let independent_sequence =
      \(carrier:A->bool) (events:(A->bool)->bool)
       (p:(A->bool)->real) (X:num->A->real).
        (!n. random_variable carrier events (X n)) /\
        (!inds:num->bool thresholds:num->real.
           FINITE inds
           ==> p
                 (carrier INTER
                  INTERS
                    (IMAGE
                      (\i. {a:A | a IN carrier /\
                                    X i a <= thresholds i})
                      inds)) =
               product inds
                 (\i. p {a:A | a IN carrier /\
                                  X i a <= thresholds i})) in
   let nonnegative_expectation =
      \(p:(A->bool)->real) (carrier:A->bool) (Y:A->real) e.
        (!a. a IN carrier ==> &0 <= Y a) /\
        seq_tends
          (\n. inv(&(2 EXP n)) *
               sum {k:num | 1 <= k /\ k <= n * 2 EXP n}
                 (\k. p {a:A | a IN carrier /\
                                  &k / &(2 EXP n) <= Y a}))
          e in
   let has_expectation =
      \(p:(A->bool)->real) (carrier:A->bool) (Y:A->real) e.
        ?ep en.
          nonnegative_expectation p carrier
            (\a. if &0 <= Y a then Y a else &0) ep /\
          nonnegative_expectation p carrier
            (\a. if Y a < &0 then --(Y a) else &0) en /\
          e = ep - en in
   let derivative_at =
      \(g:real->real) dg x.
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !h. &0 < abs h /\ abs h < d
                        ==> abs((g(x + h) - g x) / h - dg) < e in
   let standard_normal_cdf =
      @Phi:real->real.
        ?phi:real->real.
          (!x. &0 < phi x) /\
          (!x. derivative_at phi (--(x * phi x)) x) /\
          (!x. derivative_at Phi (phi x) x) /\
          (!e. &0 < e
               ==> ?B. &0 < B /\
                       !x. x < --B ==> abs(Phi x) < e) /\
          (!e. &0 < e
               ==> ?B. &0 < B /\
                       !x. B < x ==> abs(Phi x - &1) < e) in
   !carrier:A->bool
    events:(A->bool)->bool
    p:(A->bool)->real
    X:num->A->real
    mu:real->real
    sigma:real
    S:num->A->real.
      probability_space carrier events p /\
      independent_sequence carrier events p X /\
      (!n. has_expectation p carrier (X n) (&0)) /\
      &0 < sigma /\
      (!n. has_expectation p carrier
             (\a:A. X n a pow 2) (sigma pow 2)) /\
      (!n x. p {a:A | a IN carrier /\ X n a <= x} = mu x) /\
      (!n a. S n a = sum {i:num | i < n} (\i. X i a))
      ==> !x:real.
            seq_tends
              (\n. p
                {a:A |
                  a IN carrier /\
                  S n a /
                    (@r:real.
                       &0 <= r /\ r pow 2 = &n * sigma pow 2) <= x})
              (standard_normal_cdf x)`;;

let HUNDRED_THEOREMS_047_CENTRAL_LIMIT_THEOREM =
 `let seq_tends =
      \(u:num->real) l.
        !e. &0 < e ==> ?N. !n. N <= n ==> abs(u n - l) < e in
   let probability_space =
      \(carrier:A->bool) (events:(A->bool)->bool)
       (p:(A->bool)->real).
        (!s. s IN events ==> s SUBSET carrier) /\
        {} IN events /\
        carrier IN events /\
        (!s. s IN events ==> carrier DIFF s IN events) /\
        (!sets:num->A->bool.
           (!n. sets n IN events)
           ==> {a:A | ?n. a IN sets n} IN events) /\
        p {} = &0 /\
        p carrier = &1 /\
        (!s. s IN events ==> &0 <= p s) /\
        (!sets:num->A->bool.
           (!n. sets n IN events) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> seq_tends
                 (\n. sum {k:num | k < n} (\k. p (sets k)))
                 (p {a:A | ?k. a IN sets k})) in
   let random_variable =
      \(carrier:A->bool) (events:(A->bool)->bool) (Y:A->real).
        !x. {a:A | a IN carrier /\ Y a <= x} IN events in
   let independent_sequence =
      \(carrier:A->bool) (events:(A->bool)->bool)
       (p:(A->bool)->real) (X:num->A->real).
        (!n. random_variable carrier events (X n)) /\
        (!inds:num->bool thresholds:num->real.
           FINITE inds
           ==> p
                 (carrier INTER
                  INTERS
                    (IMAGE
                      (\i. {a:A | a IN carrier /\
                                    X i a <= thresholds i})
                      inds)) =
               product inds
                 (\i. p {a:A | a IN carrier /\
                                  X i a <= thresholds i})) in
   let nonnegative_expectation =
      \(p:(A->bool)->real) (carrier:A->bool) (Y:A->real) e.
        (!a. a IN carrier ==> &0 <= Y a) /\
        seq_tends
          (\n. inv(&(2 EXP n)) *
               sum {k:num | 1 <= k /\ k <= n * 2 EXP n}
                 (\k. p {a:A | a IN carrier /\
                                  &k / &(2 EXP n) <= Y a}))
          e in
   let has_expectation =
      \(p:(A->bool)->real) (carrier:A->bool) (Y:A->real) e.
        ?ep en.
          nonnegative_expectation p carrier
            (\a. if &0 <= Y a then Y a else &0) ep /\
          nonnegative_expectation p carrier
            (\a. if Y a < &0 then --(Y a) else &0) en /\
          e = ep - en in
   let derivative_at =
      \(g:real->real) dg x.
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !h. &0 < abs h /\ abs h < d
                        ==> abs((g(x + h) - g x) / h - dg) < e in
   let standard_normal_cdf =
      @Phi:real->real.
        ?phi:real->real.
          (!x. &0 < phi x) /\
          (!x. derivative_at phi (--(x * phi x)) x) /\
          (!x. derivative_at Phi (phi x) x) /\
          (!e. &0 < e
               ==> ?B. &0 < B /\
                       !x. x < --B ==> abs(Phi x) < e) /\
          (!e. &0 < e
               ==> ?B. &0 < B /\
                       !x. B < x ==> abs(Phi x - &1) < e) in
   !carrier:A->bool
    events:(A->bool)->bool
    p:(A->bool)->real
    X:num->A->real
    mu:real->real
    sigma:real
    m:real
    S:num->A->real
    Xc:num->A->real.
      probability_space carrier events p /\
      independent_sequence carrier events p X /\
      (!n. has_expectation p carrier (X n) m) /\
      &0 < sigma /\
      (!n. ?second.
             has_expectation p carrier
               (\a:A. X n a pow 2) second) /\
      (!n. has_expectation p carrier
             (\a:A. (X n a - m) pow 2) (sigma pow 2)) /\
      (!n x. p {a:A | a IN carrier /\ X n a <= x} = mu x) /\
      (!i a. Xc i a = X i a - m)
      ==> !x:real.
            seq_tends
              (\n. p
                {a:A |
                  a IN carrier /\
                  sum {i:num | i < n} (\i. Xc i a) /
                    (@r:real.
                       &0 <= r /\ r pow 2 = &n * sigma pow 2) <= x})
              (standard_normal_cdf x)`;;
