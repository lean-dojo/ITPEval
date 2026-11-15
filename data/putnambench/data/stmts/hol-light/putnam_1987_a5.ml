(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1987_a5:
  nonexistence of a vector field with continuous partial derivatives and zero
  curl on punctured three-space whose restriction to the coordinate plane is
  the prescribed rational field. This file contains no proof.
*)

let statement =
  `let punctured = {x:real^3 | ~(x = vec 0)} in
   let xrepl =
     \(x:real^3) (i:num) (t:real).
       (lambda k. if k = i then t else x$k):real^3 in
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
     \(h:real^3->real) (i:num) (x:real^3).
       @d:real.
         has_derivative_at
           (\t:real. h (xrepl x i t)) d (x$i) in
   let continuous_on_punctured =
     \(h:real^3->real).
       !x:real^3.
         x IN punctured
         ==> !e:real.
               &0 < e
               ==> ?delta:real.
                     &0 < delta /\
                     !y:real^3.
                       y IN punctured /\
                       (!k:num.
                          1 <= k /\ k <= 3
                          ==> abs (y$k - x$k) < delta)
                       ==> abs (h y - h x) < e in
   let c1_on_punctured =
     \(field:real^3->real^3).
       (!i j:num.
          1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
          ==> !x:real^3.
                x IN punctured
                ==> has_derivative_at
                      (\t:real. (field (xrepl x j t))$i)
                      (partial (\y:real^3. (field y)$i) j x)
                      (x$j)) /\
       (!i j:num.
          1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
          ==> continuous_on_punctured
                (partial (\x:real^3. (field x)$i) j)) in
   let curl =
     \(field:real^3->real^3) (x:real^3).
       (lambda i.
          if i = 1 then
            partial (\y:real^3. (field y)$3) 2 x -
            partial (\y:real^3. (field y)$2) 3 x
          else if i = 2 then
            partial (\y:real^3. (field y)$1) 3 x -
            partial (\y:real^3. (field y)$3) 1 x
          else
            partial (\y:real^3. (field y)$2) 1 x -
            partial (\y:real^3. (field y)$1) 2 x):real^3 in
   let G =
     \(v:real^2).
       (lambda i.
          if i = 1 then
            --(v$2) / ((v$1) pow 2 + &4 * (v$2) pow 2)
          else if i = 2 then
            (v$1) / ((v$1) pow 2 + &4 * (v$2) pow 2)
          else &0):real^3 in
   ~(?field:real^3->real^3.
       c1_on_punctured field /\
       (!x:real^3. x IN punctured ==> curl field x = vec 0) /\
       (!x y:real.
          field ((lambda i.
                    if i = 1 then x else if i = 2 then y else &0):real^3) =
          G ((lambda i.
                if i = 1 then x else y):real^2)))`;;
