(*
  Statement-only formalization of miniF2F valid problem amc12a_2016_p3. This file contains no
  proof.
*)

needs "Library/floor.ml";;

let amc12a_2016_p3 =
  `!f:real->real->real.
     (!x y:real.
        ~(y = &0)
        ==> f x y = x - y * floor (x / y))
     ==> f (&3 / &8) (-- (&2 / &5)) = -- (&1 / &40)`;;
