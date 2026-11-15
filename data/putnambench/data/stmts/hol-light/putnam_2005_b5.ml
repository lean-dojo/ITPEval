(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2005_b5:
  a real multivariate polynomial that is harmonic and divisible by the sum
  of the squares of its variables is identically zero. This file contains no
  proof.
*)

let statement =
  `let xrepl =
     \(x:real^N) (i:num) (t:real).
       (lambda k. if k = i then t else x$k):real^N in
   let has_derivative_at =
     \(h:real->real) (d:real) (a:real).
       !e:real.
         &0 < e
         ==> ?delta:real.
               &0 < delta /\
               !y:real.
                 &0 < abs (y - a) /\ abs (y - a) < delta
                 ==> abs ((h y - h a) / (y - a) - d) < e in
   let partial =
     \(P:real^N->real) (i:num) (x:real^N).
       @d:real.
         has_derivative_at
           (\t:real. P (xrepl x i t)) d (x$i) in
   let coordinate_second_derivative =
     \(P:real^N->real) (i:num) (x:real^N).
       partial (\y:real^N. partial P i y) i x in
   let is_polynomial =
     \(P:real^N->real).
       ?s:(num^N)->bool. ?c:(num^N)->real.
         FINITE s /\
         !x:real^N.
           P x =
           sum s
             (\m:num^N.
                c m *
                product (1..dimindex(:N))
                  (\i:num. (x$i) pow (m$i))) in
   !n:num. !P:real^N->real.
     dimindex(:N) = n /\
     0 < n /\
     is_polynomial P /\
     (!x:real^N.
        sum (1..n) (\i:num. coordinate_second_derivative P i x) = &0) /\
     (?Q:real^N->real.
        is_polynomial Q /\
        !x:real^N.
          sum (1..n) (\i:num. (x$i) pow 2) * Q x = P x)
     ==> P = (\x:real^N. &0)`;;
