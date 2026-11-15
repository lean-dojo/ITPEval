(*
  Statement-only formalization of PutnamBench artifact putnam_1964_b3:
  convergence to zero at positive infinity of a continuous real function
  whose samples along every positive arithmetic ray converge to zero. This
  file contains no proof.
*)

let statement =
  `let continuous =
     \(f:real->real).
       !x e:real.
         &0 < e
         ==> ?d:real.
               &0 < d /\
               !y:real. abs (y - x) < d ==> abs (f y - f x) < e in
   let tends_seq_zero =
     \(u:num->real).
       !e:real.
         &0 < e
         ==> ?N:num. !n:num. N <= n ==> abs (u n) < e in
   let tends_at_posinfinity_zero =
     \(f:real->real).
       !e:real.
         &0 < e
         ==> ?B:real. !x:real. B <= x ==> abs (f x) < e in
   !f:real->real.
     continuous f /\
     (!alpha:real.
        &0 < alpha
        ==> tends_seq_zero (\n:num. f (&n * alpha)))
     ==> tends_at_posinfinity_zero f`;;
