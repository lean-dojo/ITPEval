(*
  Statement-only formalization of miniF2F test problem amc12a_2021_p12.
  This file contains no proof.
*)

needs "Complex/complexnumbers.ml";;

let statement =
  `!a:real b:real c:real d:real f:complex->complex.
     (!z. f z =
          z pow 6 - Cx (&10) * z pow 5 + Cx a * z pow 4 +
          Cx b * z pow 3 + Cx c * z pow 2 + Cx d * z + Cx (&16)) /\
     (!z. f z = Cx (&0)
          ==> Im z = &0 /\ &0 < Re z /\ integer (Re z))
     ==> b = --(&88)`;;
