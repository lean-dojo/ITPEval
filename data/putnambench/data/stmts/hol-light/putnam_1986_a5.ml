(*
  Statement-only formalization of PutnamBench artifact putnam_1986_a5:
  a vector field with continuous second-order partial derivatives and
  constant cross-partial differences has a scalar correction making every
  component linear. This file contains no proof.
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
     \(h:real^N->real) (i:num) (x:real^N).
       @d:real.
         has_derivative_at
           (\t:real. h (xrepl x i t)) d (x$i) in
   let continuous =
     \(h:real^N->real).
       !x:real^N. !e:real.
         &0 < e
         ==> ?delta:real.
               &0 < delta /\
               !y:real^N.
                 (!k:num.
                    1 <= k /\ k <= dimindex(:N)
                    ==> abs (y$k - x$k) < delta)
                 ==> abs (h y - h x) < e in
   let contdiff2 =
     \(h:real^N->real).
       (!i:num. 1 <= i /\ i <= dimindex(:N)
                ==> !x:real^N.
                      has_derivative_at
                        (\t:real. h (xrepl x i t))
                        (partial h i x) (x$i)) /\
       (!i:num. 1 <= i /\ i <= dimindex(:N)
                ==> continuous (partial h i)) /\
       (!i j:num.
          1 <= i /\ i <= dimindex(:N) /\
          1 <= j /\ j <= dimindex(:N)
          ==> !x:real^N.
                has_derivative_at
                  (\t:real. partial h i (xrepl x j t))
                  (partial (partial h i) j x) (x$j)) /\
       (!i j:num.
          1 <= i /\ i <= dimindex(:N) /\
          1 <= j /\ j <= dimindex(:N)
          ==> continuous (partial (partial h i) j)) in
   let linear_real =
     \(h:real^N->real).
       ?a:real^N.
         !x:real^N.
           h x =
           sum (1..dimindex(:N)) (\k:num. a$k * x$k) in
   !n:num. !f:real^N->real^N.
     dimindex(:N) = n /\
     1 <= n /\
     (!i:num.
        1 <= i /\ i <= n
        ==> contdiff2 (\x:real^N. (f x)$i)) /\
     (?c:real^N^N.
        !i j:num.
          1 <= i /\ i <= n /\ 1 <= j /\ j <= n
          ==> !x:real^N.
                partial (\y:real^N. (f y)$i) j x -
                partial (\y:real^N. (f y)$j) i x =
                c$i$j)
     ==> ?g:real^N->real.
           !i:num.
             1 <= i /\ i <= n
             ==> linear_real
                   (\x:real^N.
                      (f x)$i + partial g i x)`;;
