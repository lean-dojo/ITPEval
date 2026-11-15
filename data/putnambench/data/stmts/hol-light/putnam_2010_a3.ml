(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2010_a3:
  a bounded real-valued C1 function on the real plane satisfying a constant-
  coefficient first-order linear partial differential equation is identically
  zero. This file contains no proof.
*)

let statement =
  `let xrepl =
     \(x:real^2) (i:num) (t:real).
       (lambda k. if k = i then t else x$k):real^2 in
   let has_derivative_at =
     \(f:real->real) (d:real) (x:real).
       !e:real.
         &0 < e
         ==> ?delta:real.
               &0 < delta /\
               !y:real.
                 &0 < abs (y - x) /\ abs (y - x) < delta
                 ==> abs ((f y - f x) / (y - x) - d) < e in
   let partial =
     \(h:real^2->real) (i:num) (x:real^2).
       @d:real.
         has_derivative_at
           (\t:real. h (xrepl x i t)) d (x$i) in
   let continuous =
     \(f:real^2->real).
       !x:real^2. !e:real.
         &0 < e
         ==> ?delta:real.
               &0 < delta /\
               !y:real^2.
                 (!i:num.
                    1 <= i /\ i <= 2
                    ==> abs (y$i - x$i) < delta)
                 ==> abs (f y - f x) < e in
   let continuously_differentiable =
     \(h:real^2->real).
       (!i:num.
          1 <= i /\ i <= 2
          ==> (!x:real^2.
                 has_derivative_at
                   (\t:real. h (xrepl x i t))
                   (partial h i x) (x$i)) /\
              continuous (partial h i)) in
   !h:real^2->real. !a b M:real.
     continuously_differentiable h /\
     (!x:real^2.
        h x = a * partial h 1 x + b * partial h 2 x) /\
     (!x:real^2. abs (h x) <= M)
     ==>
     h = (\x:real^2. &0)`;;
