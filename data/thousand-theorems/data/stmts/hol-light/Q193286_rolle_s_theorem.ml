(*
  Statement-only formalization of Thousand Theorems corpus artifact Q193286,
  "Rolle's theorem": a real function continuous on a closed interval with
  equal endpoint values has an interior point where its derivative, totalized
  to zero at nondifferentiable points, is zero. This file contains no proof.
*)

let Q193286_ROLLE_S_THEOREM =
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
   let total_derivative =
      \(f:real->real) (x:real).
        if (?d:real. has_derivative_at f d x)
        then (@d:real. has_derivative_at f d x)
        else &0 in
   !(f:real->real) a b.
     a < b /\
     continuous_on_interval f a b /\
     f a = f b
     ==> ?c. a < c /\ c < b /\ total_derivative f c = &0`;;
