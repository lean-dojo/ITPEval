(*
  Statement-only formalization of "Fair Games Theorem (Optional Stopping)"
  from Hundred Theorems artifact 062 (hundred-theorems__hol-light__062).
  It states both the bounded-stopping-time characterization of submartingales
  and the fair-game expectation conclusions for martingales, submartingales,
  and supermartingales under the standard optional-stopping hypotheses. This
  file contains no proof.
*)

let HUNDRED_THEOREMS_062_FAIR_GAMES_THEOREM =
 `let seq_tends =
      \(u:num->real) l.
        !e. &0 < e ==> ?N. !n. N <= n ==> abs(u n - l) < e in
   let sigma_algebra =
      \(carrier:A->bool) (events:(A->bool)->bool).
        (!s. s IN events ==> s SUBSET carrier) /\
        {} IN events /\
        carrier IN events /\
        (!s. s IN events ==> carrier DIFF s IN events) /\
        (!sets:num->A->bool.
           (!n. sets n IN events)
           ==> {x:A | ?n. x IN sets n} IN events) in
   let probability_space =
      \(carrier:A->bool) (events:(A->bool)->bool)
       (p:(A->bool)->real).
        sigma_algebra carrier events /\
        p {} = &0 /\
        p carrier = &1 /\
        (!s. s IN events ==> &0 <= p s) /\
        (!sets:num->A->bool.
           (!n. sets n IN events) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> seq_tends
                 (\n. sum {k:num | k < n} (\k. p (sets k)))
                 (p {x:A | ?k. x IN sets k})) in
   let random_variable =
      \(carrier:A->bool) (events:(A->bool)->bool) (Y:A->real).
        !r. {x:A | x IN carrier /\ Y x <= r} IN events in
   let filtration =
      \(carrier:A->bool) (events:(A->bool)->bool)
       (FF:num->(A->bool)->bool).
        (!n. sigma_algebra carrier (FF n) /\ FF n SUBSET events) /\
        (!m n. m <= n ==> FF m SUBSET FF n) in
   let adapted =
      \(carrier:A->bool) (FF:num->(A->bool)->bool)
       (X:num->A->real).
        !n. random_variable carrier (FF n) (X n) in
   let nonnegative_expectation =
      \(p:(A->bool)->real) (carrier:A->bool) (Y:A->real) e.
        (!x. x IN carrier ==> &0 <= Y x) /\
        seq_tends
          (\n. inv(&(2 EXP n)) *
               sum {k:num | 1 <= k /\ k <= n * 2 EXP n}
                 (\k. p {x:A | x IN carrier /\
                                  &k / &(2 EXP n) <= Y x}))
          e in
   let has_expectation =
      \(p:(A->bool)->real) (carrier:A->bool) (Y:A->real) e.
        ?ep en.
          nonnegative_expectation p carrier
            (\x. if &0 <= Y x then Y x else &0) ep /\
          nonnegative_expectation p carrier
            (\x. if Y x < &0 then --(Y x) else &0) en /\
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
          {x:A | x IN carrier /\ ~(P x)} SUBSET negligible in
   let indicator =
      \(a:A->bool) x. if x IN a then &1 else &0 in
   let martingale =
      \(carrier:A->bool) (events:(A->bool)->bool)
       (p:(A->bool)->real) (FF:num->(A->bool)->bool)
       (X:num->A->real).
        filtration carrier events FF /\
        adapted carrier FF X /\
        (!n. integrable p carrier (X n)) /\
        (!n a. a IN FF n
          ==> expectation p carrier
                (\x. X (SUC n) x * indicator a x) =
              expectation p carrier
                (\x. X n x * indicator a x)) in
   let submartingale =
      \(carrier:A->bool) (events:(A->bool)->bool)
       (p:(A->bool)->real) (FF:num->(A->bool)->bool)
       (X:num->A->real).
        filtration carrier events FF /\
        adapted carrier FF X /\
        (!n. integrable p carrier (X n)) /\
        (!n a. a IN FF n
          ==> expectation p carrier
                (\x. X n x * indicator a x) <=
              expectation p carrier
                (\x. X (SUC n) x * indicator a x)) in
   let supermartingale =
      \(carrier:A->bool) (events:(A->bool)->bool)
       (p:(A->bool)->real) (FF:num->(A->bool)->bool)
       (X:num->A->real).
        filtration carrier events FF /\
        adapted carrier FF X /\
        (!n. integrable p carrier (X n)) /\
        (!n a. a IN FF n
          ==> expectation p carrier
                (\x. X (SUC n) x * indicator a x) <=
              expectation p carrier
                (\x. X n x * indicator a x)) in
   let stopping_time =
      \(carrier:A->bool) (FF:num->(A->bool)->bool) (tau:A->num).
        !n. {x:A | x IN carrier /\ tau x <= n} IN FF n in
   let option_stopping_time =
      \(carrier:A->bool) (FF:num->(A->bool)->bool)
       (tau:A->num option).
        !n. {x:A | x IN carrier /\
                    ?k. tau x = SOME k /\ k <= n} IN FF n in
   let option_stopped_value =
      \(X:num->A->real) (tau:A->num option) x.
        X (@n. tau x = SOME n) x in
   let optional_stopping_conditions =
      \(carrier:A->bool) (events:(A->bool)->bool)
       (p:(A->bool)->real) (X:num->A->real) (tau:A->num option).
        (?N. almost_surely carrier events p
               (\x. ?k. tau x = SOME k /\ k <= N)) \/
        (almost_surely carrier events p
           (\x. ?k. tau x = SOME k) /\
         ?K. !n. almost_surely carrier events p
                    (\x. abs(X n x) < K)) \/
        (almost_surely carrier events p
           (\x. ?k. tau x = SOME k) /\
         integrable p carrier (\x. &(@n. tau x = SOME n)) /\
         ?K. !n. almost_surely carrier events p
                    (\x. abs(X (SUC n) x - X n x) <= K)) in
   (!carrier:A->bool
     events:(A->bool)->bool
     p:(A->bool)->real
     FF:num->(A->bool)->bool
     X:num->A->real.
       probability_space carrier events p /\
       filtration carrier events FF /\
       adapted carrier FF X /\
       (!n. integrable p carrier (X n))
       ==>
       (submartingale carrier events p FF X <=>
        !sigma tau:A->num.
          stopping_time carrier FF sigma /\
          stopping_time carrier FF tau /\
          (!x. x IN carrier ==> sigma x <= tau x) /\
          (?N. !x. x IN carrier ==> tau x <= N)
          ==> expectation p carrier (\x. X (sigma x) x) <=
              expectation p carrier (\x. X (tau x) x))) /\
   (!carrier:A->bool
     events:(A->bool)->bool
     p:(A->bool)->real
     FF:num->(A->bool)->bool
     tau:A->num option
     X:num->A->real.
       probability_space carrier events p /\
       filtration carrier events FF /\
       option_stopping_time carrier FF tau /\
       adapted carrier FF X /\
       (!n. integrable p carrier (X n)) /\
       optional_stopping_conditions carrier events p X tau
       ==>
       (integrable p carrier (option_stopped_value X tau) /\
        (martingale carrier events p FF X
         ==> expectation p carrier (option_stopped_value X tau) =
             expectation p carrier (X 0)) /\
        (submartingale carrier events p FF X
         ==> expectation p carrier (X 0) <=
             expectation p carrier (option_stopped_value X tau)) /\
        (supermartingale carrier events p FF X
         ==> expectation p carrier (option_stopped_value X tau) <=
             expectation p carrier (X 0))))`;;
