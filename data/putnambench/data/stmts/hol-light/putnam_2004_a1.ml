(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2004_a1:
  a running free-throw success rate that rises from below four fifths to above
  four fifths must equal four fifths at an intermediate attempt count. This
  file contains no proof.
*)

let statement =
  `!S:(num->bool)->num->real.
     (!attempts:num->bool. !N:num.
        1 <= N
        ==>
        S attempts N =
        &(nsum (0..N - 1) (\i. if attempts i then 1 else 0)) / &N)
     ==>
     ((!attempts:num->bool. !a b:num.
         1 <= a /\
         a < b /\
         S attempts a < &4 / &5 /\
         &4 / &5 < S attempts b
         ==>
         ?c:num.
           a < c /\
           c < b /\
           S attempts c = &4 / &5)
      <=> T)`;;
