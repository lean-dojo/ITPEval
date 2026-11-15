(*
  Statement-only formalization of Thousand Theorems corpus artifact Q257387,
  "Vitali theorem": the choice-defined set containing one representative of
  each rational-translation class in the real unit interval is not Borel
  measurable. This file contains no proof.
*)

let Q257387_VITALI_THEOREM =
 `let is_rational =
      \x:real.
        ?m n:num. ~(n = 0) /\ abs x = &m / &n in
   let unit_interval =
      {x:real | &0 <= x /\ x <= &1} in
   let representative =
      \x:real.
        @y:real.
          y IN unit_interval /\ is_rational (x - y) in
   let vitali_set =
      IMAGE representative unit_interval in
   let open_real =
      \u:real->bool.
        !x:real.
          x IN u
          ==> ?epsilon:real.
                &0 < epsilon /\
                !y:real.
                  abs (y - x) < epsilon ==> y IN u in
   let sigma_algebra =
      \events:(real->bool)->bool.
        events {} /\
        events (:real) /\
        (!s:real->bool.
           events s ==> events ((:real) DIFF s)) /\
        (!sets:num->real->bool.
           (!n:num. events (sets n))
           ==> events {x:real | ?n:num. x IN sets n}) in
   let borel_measurable =
      \s:real->bool.
        !events:(real->bool)->bool.
          sigma_algebra events /\
          (!u:real->bool. open_real u ==> events u)
          ==> events s in
   ~(borel_measurable vitali_set)`;;
