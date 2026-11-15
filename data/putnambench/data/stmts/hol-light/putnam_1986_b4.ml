(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1986_b4:
  the minimum distance from a positive real parameter to values
  sqrt(m^2 + 2*n^2) for integers m and n tends to zero at positive infinity.
  This file contains no proof.
*)

let statement =
  `let tends_at_posinfinity =
     \(g:real->real) (l:real).
       !e:real.
         &0 < e
         ==> ?B:real.
               !r:real. B <= r ==> abs (g r - l) < e in
   let putnam_1986_b4_solution = T in
   !G:real->real.
     ((!r:real.
         ?m n:int.
           G r =
           abs
             (r -
              sqrt
                (real_of_int
                   (m pow 2 + (&2:int) * n pow 2)))) /\
      (!r:real.
         !m n:int.
           G r <=
           abs
             (r -
              sqrt
                (real_of_int
                   (m pow 2 + (&2:int) * n pow 2)))))
     ==>
     (tends_at_posinfinity G (&0) <=> putnam_1986_b4_solution)`;;
