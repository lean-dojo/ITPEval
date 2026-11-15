(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2011_a5:
  a uniform inverse-linear bound for pairwise values of a twice continuously
  differentiable function whose gradient is parallel to a prescribed positive
  vector field. This file contains no proof.
*)

let statement =
  `let pair =
     \(u:real) (v:real).
       (lambda i. if i = 1 then u else v):real^2 in
   let xrepl =
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
   let continuous1 =
     \(f:real->real).
       !x e:real.
         &0 < e
         ==> ?delta:real.
               &0 < delta /\
               !y:real.
                 abs (y - x) < delta
                 ==> abs (f y - f x) < e in
   let continuous2 =
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
   let deriv1 =
     \(f:real->real) (x:real).
       @d:real. has_derivative_at f d x in
   let partial =
     \(f:real^2->real) (i:num) (x:real^2).
       @d:real.
         has_derivative_at
           (\t:real. f (xrepl x i t)) d (x$i) in
   let second_partial =
     \(f:real^2->real) (i:num) (j:num) (x:real^2).
       @d:real.
         has_derivative_at
           (\t:real. partial f i (xrepl x j t)) d (x$j) in
   let twice_continuously_differentiable1 =
     \(f:real->real).
       (!x:real. has_derivative_at f (deriv1 f x) x) /\
       continuous1 (deriv1 f) /\
       (!x:real.
          has_derivative_at
            (deriv1 f) (deriv1 (deriv1 f) x) x) /\
       continuous1 (deriv1 (deriv1 f)) in
   let twice_continuously_differentiable2 =
     \(f:real^2->real).
       (!i:num.
          1 <= i /\ i <= 2
          ==>
          (!x:real^2.
             has_derivative_at
               (\t:real. f (xrepl x i t))
               (partial f i x) (x$i)) /\
          continuous2 (partial f i)) /\
       (!i j:num.
          1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
          ==>
          (!x:real^2.
             has_derivative_at
               (\t:real. partial f i (xrepl x j t))
               (second_partial f i j x) (x$j)) /\
          continuous2 (second_partial f i j)) in
   !f:real^2->real. !g:real->real.
     twice_continuously_differentiable2 f /\
     twice_continuously_differentiable1 g /\
     (!u:real. f (pair u u) = &0) /\
     (!x:real. &0 < g x /\ x pow 2 * g x <= &1) /\
     (!uv:real^2.
        ?c:real.
          partial f 1 uv = c * g (uv$1) /\
          partial f 2 uv = c * --(g (uv$2)))
     ==>
     ?C:real.
       !n:num. !x:num->real.
         2 <= n
         ==>
         ?i j:num.
           i <= n /\ j <= n /\ ~(i = j) /\
           abs (f (pair (x i) (x j))) <= C / &n`;;
