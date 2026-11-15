(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2016_a6:
  the least constant bounding the absolute-value integral of every real cubic
  with a root in the unit interval by its maximum absolute value there. This
  file contains no proof.
*)

needs "Library/poly.ml";;
needs "Library/transc.ml";;

let statement =
  `let is_unit_interval_maximum =
     \(f:real->real) (m:real).
       (?x:real.
          &0 <= x /\
          x <= &1 /\
          f x = m) /\
       (!x:real.
          &0 <= x /\ x <= &1
          ==> f x <= m) in
   let admissible =
     \C:real.
       !P:real list.
         degree P = 3 /\
         (?r:real.
            &0 <= r /\
            r <= &1 /\
            poly P r = &0)
         ==>
         !M:real.
           is_unit_interval_maximum
             (\x:real. abs (poly P x)) M
           ==>
           integral(&0,&1) (\x:real. abs (poly P x)) <= C * M in
   admissible (&5 / &6) /\
   (!C:real. admissible C ==> &5 / &6 <= C)`;;
