(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2022_a4
  (putnambench__hol-light__putnam_2022_a4): the expected dyadically weighted
  sum stopped at the first non-descent of independent uniform random variables
  on [0,1] is 2 * exp(1/2) - 3. This file contains no proof.
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
          (!m n:num. ~(m = n) ==> DISJOINT (sets m) (sets n))
          ==> seq_tends
                (\n:num. sum {j:num | j < n} (\j:num. p (sets j)))
                (p {w:A | ?j:num. w IN sets j})) in
   let measurable_real =
     \(measurable:(A->bool)->bool) (f:A->real).
       !a:real. {w:A | f w < a} IN measurable in
   let uniform_unit =
     \(p:(A->bool)->real) (f:A->real).
       !a:real.
         p {w:A | f w <= a} =
         if a < &0 then &0 else if &1 < a then &1 else a in
   let independent =
     \(p:(A->bool)->real) (X:num->A->real).
       !indices:num->bool.
         FINITE indices
         ==> !threshold:num->real.
               p {w:A |
                    !i:num.
                      i IN indices ==> X i w <= threshold i} =
               product indices
                 (\i:num. p {w:A | X i w <= threshold i}) in
   !measurable:(A->bool)->bool
    p:(A->bool)->real
    X:num->A->real
    k:A->num->bool
    S:A->real.
      probability_space measurable p /\
      (!i:num. measurable_real measurable (X i)) /\
      (!i:num. uniform_unit p (X i)) /\
      independent p X /\
      (!w:A. !i:num.
         (k w i <=> !l:num. l < i ==> X l w > X (l + 1) w)) /\
      (!w:A.
         S w =
         suminf
           (\i:num.
              if k w i
              then X i w / ((&2) pow (i + 1))
              else &0)) /\
      measurable_real measurable S
      ==>
      integral(&0,&1) (\t:real. p {w:A | t < S w}) =
      &2 * exp (&1 / &2) - &3`;;
