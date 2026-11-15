(*
  Statement-only formalization of Thousand Theorems corpus artifact Q189136,
  "Mean value theorem": Lagrange's and Cauchy's mean value theorems for
  real-valued functions on a real interval. This file contains no proof.
*)

let Q189136_MEAN_VALUE_THEOREM =
 `let continuous_on_interval =
      \(f:real->real) (a:real) (b:real).
        !x:real.
          a <= x /\ x <= b
          ==> !epsilon:real.
                &0 < epsilon
                ==> ?delta:real.
                      &0 < delta /\
                      !y:real.
                        a <= y /\ y <= b /\ abs(y - x) < delta
                        ==> abs(f y - f x) < epsilon in
   let has_derivative_at =
      \(f:real->real) (d:real) (x:real).
        !epsilon:real.
          &0 < epsilon
          ==> ?delta:real.
                &0 < delta /\
                !y:real.
                  &0 < abs(y - x) /\ abs(y - x) < delta
                  ==> abs((f y - f x) / (y - x) - d) < epsilon in
   let differentiable_on_open_interval =
      \(f:real->real) (a:real) (b:real).
        !x:real.
          a < x /\ x < b
          ==> ?d:real. has_derivative_at f d x in
   let total_derivative =
      \(f:real->real) (x:real).
        if (?d:real. has_derivative_at f d x)
        then (@d:real. has_derivative_at f d x)
        else &0 in
   ((!f:real->real. !a b:real.
       a < b /\
       continuous_on_interval f a b /\
       differentiable_on_open_interval f a b
       ==> ?c:real.
             a < c /\ c < b /\
             total_derivative f c = (f b - f a) / (b - a))
    /\
    (!f g:real->real. !a b:real.
       a < b /\
       continuous_on_interval f a b /\
       continuous_on_interval g a b /\
       differentiable_on_open_interval f a b /\
       differentiable_on_open_interval g a b
       ==> ?c:real.
             a < c /\ c < b /\
             (g b - g a) * total_derivative f c =
             (f b - f a) * total_derivative g c))`;;
