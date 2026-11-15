(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_b4
  (putnambench__hol-light__putnam_2024_b4): the limiting normalized expected
  state of the integer random walk driven by independent uniform choices from
  1 through n is (1 - exp(-2))/2. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let seq_tends =
     \(u:num->real) l.
       !e:real.
         &0 < e
         ==> ?N:num. !n:num. N <= n ==> abs (u n - l) < e in
   let sigma_algebra =
     \(measurable:(A->bool)->bool).
       {} IN measurable /\
       (:A) IN measurable /\
       (!s:A->bool.
          s IN measurable ==> (:A) DIFF s IN measurable) /\
       (!sets:num->A->bool.
          (!n:num. sets n IN measurable)
          ==> {w:A | ?n:num. w IN sets n} IN measurable) in
   let probability_space =
     \(measurable:(A->bool)->bool) (p:(A->bool)->real).
       sigma_algebra measurable /\
       p {} = &0 /\
       p (:A) = &1 /\
       (!s:A->bool. s IN measurable ==> &0 <= p s) /\
       (!sets:num->A->bool.
          (!n:num. sets n IN measurable) /\
          (!j k:num. ~(j = k) ==> DISJOINT (sets j) (sets k))
          ==> seq_tends
                (\n:num. sum {j:num | j < n} (\j:num. p (sets j)))
                (p {w:A | ?j:num. w IN sets j})) in
   let integer_random_variable =
     \(measurable:(A->bool)->bool) (X:A->int).
       !s:int->bool. {w:A | X w IN s} IN measurable in
   let uniform_integer =
     \(measurable:(A->bool)->bool)
      (p:(A->bool)->real)
      (n:num)
      (X:A->int).
       integer_random_variable measurable X /\
       (!s:int->bool.
          p {w:A | X w IN s} =
          &(CARD {z:int |
                    z IN s /\ (&1:int) <= z /\ z <= &n}) / &n) in
   let independent =
     \(p:(A->bool)->real) (X:num->num->A->int).
       !indices:(num#num)->bool.
         FINITE indices
         ==> !sets:(num#num)->int->bool.
               p {w:A |
                    !i:num#num.
                      i IN indices
                      ==> X (FST i) (SND i) w IN sets i} =
               product indices
                 (\i:num#num.
                    p {w:A | X (FST i) (SND i) w IN sets i}) in
   let enumerate_int =
     \j:num.
       if EVEN j
       then (&(j DIV 2):int)
       else --(&(j DIV 2 + 1):int) in
   let expectation =
     \(p:(A->bool)->real) (X:A->int).
       suminf
         (\j:num.
            real_of_int (enumerate_int j) *
            p {w:A | X w = enumerate_int j}) in
   !measurable:(A->bool)->bool
    p:(A->bool)->real
    m:num->num->A->int
    a:num->num->A->int.
      probability_space measurable p /\
      (!n:num.
         0 < n ==> !w:A. a n 0 w = (&1:int)) /\
      (!n k:num.
         0 < n ==> uniform_integer measurable p n (m n k)) /\
      (!n k:num. !w:A.
         0 < n
         ==> a n (k + 1) w =
             if m n k w > a n k w then
               a n k w + (&1:int)
             else if m n k w = a n k w then
               a n k w
             else
               a n k w - (&1:int)) /\
      independent p m
      ==>
      seq_tends
        (\n:num. expectation p (a n n) / &n)
        ((&1 - exp (-- &2)) / &2)`;;
