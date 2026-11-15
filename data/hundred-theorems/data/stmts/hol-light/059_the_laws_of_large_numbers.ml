(*
  Statement-only formalization of "The Laws of Large Numbers" from Hundred
  Theorems artifact 059 (hundred-theorems__hol-light__059). It states the
  strong law for a sequence of pairwise independent, identically distributed,
  integrable real random variables: their sample averages converge almost
  surely to the common expectation. This file contains no proof.
*)

let HUNDRED_THEOREMS_059_STRONG_LAW_OF_LARGE_NUMBERS =
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
   let pairwise_independent =
      \(carrier:A->bool) (events:(A->bool)->bool)
       (p:(A->bool)->real) (X:num->A->real).
        (!n. random_variable carrier events (X n)) /\
        (!i j s t. ~(i = j)
           ==> p {a:A | a IN carrier /\ X i a <= s /\ X j a <= t} =
               p {a:A | a IN carrier /\ X i a <= s} *
               p {a:A | a IN carrier /\ X j a <= t}) in
   let identically_distributed =
      \(carrier:A->bool) (p:(A->bool)->real) (X:num->A->real).
        !n t.
          p {a:A | a IN carrier /\ X n a <= t} =
          p {a:A | a IN carrier /\ X 0 a <= t} in
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
   let integrable =
      \(p:(A->bool)->real) (carrier:A->bool) (Y:A->real).
        ?e. has_expectation p carrier Y e in
   let expectation =
      \(p:(A->bool)->real) (carrier:A->bool) (Y:A->real).
        @e. has_expectation p carrier Y e in
   let almost_surely =
      \(carrier:A->bool) (events:(A->bool)->bool)
       (p:(A->bool)->real) (P:A->bool).
        ?negligible:A->bool.
          negligible IN events /\
          p negligible = &0 /\
          {a:A | a IN carrier /\ ~(P a)} SUBSET negligible in
   !carrier:A->bool
    events:(A->bool)->bool
    p:(A->bool)->real
    X:num->A->real.
      probability_space carrier events p /\
      pairwise_independent carrier events p X /\
      identically_distributed carrier p X /\
      integrable p carrier (X 0)
      ==> almost_surely carrier events p
            (\a. seq_tends
                   (\n. inv(&n) *
                        sum {i:num | i < n} (\i. X i a))
                   (expectation p carrier (X 0)))`;;
