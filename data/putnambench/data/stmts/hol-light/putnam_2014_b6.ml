(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2014_b6:
  a Lipschitz real function on the unit interval with integer-affine values at
  rational inputs is affine on each member of a finite interval cover. This
  file contains no proof.
*)

let statement =
  `let unit_interval = {x:real | &0 <= x /\ x <= &1} in
   let is_rational =
     \x:real.
       ?p q:int.
         ~(q = (&0:int)) /\
         x = real_of_int p / real_of_int q in
   let closed_interval =
     \a b:real. {x:real | a <= x /\ x <= b} in
   !f:real->real.
     (?K:real.
        &0 < K /\
        !x y:real.
          x IN unit_interval /\ y IN unit_interval
          ==> abs (f x - f y) <= K * abs (x - y)) /\
     (!r:real.
        r IN unit_interval /\ is_rational r
        ==> ?a b:int.
              f r = real_of_int a + real_of_int b * r)
     ==>
     ?intervals:(real->bool)->bool.
       FINITE intervals /\
       (!interval:real->bool.
          interval IN intervals
          ==> ?a b m c:real.
                a <= b /\
                interval = closed_interval a b /\
                !x:real. x IN interval ==> f x = c + m * x) /\
       UNIONS intervals = unit_interval`;;
