(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1137206,
  "Taylor's theorem": the Lagrange and Cauchy remainder formulas for the
  Taylor polynomial of a real function on a closed interval. This file
  contains no proof.
*)

let q1137206_has_derivative_within = new_definition
  `q1137206_has_derivative_within
     (f:real->real) (s:real->bool) (a:real) (d:real) <=>
     !epsilon:real.
       &0 < epsilon
       ==> ?delta:real.
             &0 < delta /\
             !y:real.
               y IN s /\ ~(y = a) /\ abs (y - a) < delta
               ==> abs ((f y - f a) / (y - a) - d) < epsilon`;;

let q1137206_derivative_within = new_definition
  `q1137206_derivative_within
     (f:real->real) (s:real->bool) (a:real) =
     if (?d:real. q1137206_has_derivative_within f s a d) /\
        (!d e:real.
           q1137206_has_derivative_within f s a d /\
           q1137206_has_derivative_within f s a e
           ==> d = e)
     then @d:real. q1137206_has_derivative_within f s a d
     else &0`;;

let q1137206_iterated_derivative_within =
  new_recursive_definition num_RECURSION
  `q1137206_iterated_derivative_within 0 f s = (f:real->real) /\
   (!n.
      q1137206_iterated_derivative_within (SUC n) f s =
      \a:real.
        q1137206_derivative_within
          (q1137206_iterated_derivative_within n f s) s a)`;;

let q1137206_continuous_on = new_definition
  `q1137206_continuous_on (f:real->real) (s:real->bool) <=>
     !a:real.
       a IN s
       ==> !epsilon:real.
             &0 < epsilon
             ==> ?delta:real.
                   &0 < delta /\
                   !y:real.
                     y IN s /\ abs (y - a) < delta
                     ==> abs (f y - f a) < epsilon`;;

let q1137206_differentiable_on = new_definition
  `q1137206_differentiable_on (f:real->real) (s:real->bool) <=>
     !a:real.
       a IN s
       ==> ?d:real. q1137206_has_derivative_within f s a d`;;

let q1137206_cont_diff_on = new_definition
  `q1137206_cont_diff_on
     (n:num) (f:real->real) (s:real->bool) <=>
     (!k:num.
        k <= n
        ==> q1137206_continuous_on
              (q1137206_iterated_derivative_within k f s) s) /\
     (!k:num.
        k < n
        ==> q1137206_differentiable_on
              (q1137206_iterated_derivative_within k f s) s)`;;

let q1137206_taylor_polynomial = new_definition
  `q1137206_taylor_polynomial
     (n:num) (f:real->real) (s:real->bool) (x0:real) (x:real) =
     sum (0..n)
       (\k:num.
          q1137206_iterated_derivative_within k f s x0 *
          (x - x0) pow k / &(FACT k))`;;

let Q1137206_TAYLOR_S_THEOREM =
  `!f:real->real. !x x0:real. !n:num.
     let closed_interval = {t:real | x0 <= t /\ t <= x} in
     let open_interval = {t:real | x0 < t /\ t < x} in
     x0 < x /\
     q1137206_cont_diff_on n f closed_interval /\
     q1137206_differentiable_on
       (q1137206_iterated_derivative_within n f closed_interval)
       open_interval
     ==>
     (?x':real.
        x' IN open_interval /\
        f x -
        q1137206_taylor_polynomial n f closed_interval x0 x =
        q1137206_iterated_derivative_within
          (SUC n) f closed_interval x' *
        (x - x0) pow (SUC n) / &(FACT (SUC n))) /\
     (?x':real.
        x' IN open_interval /\
        f x -
        q1137206_taylor_polynomial n f closed_interval x0 x =
        q1137206_iterated_derivative_within
          (SUC n) f closed_interval x' *
        (x - x') pow n / &(FACT n) * (x - x0))`;;
