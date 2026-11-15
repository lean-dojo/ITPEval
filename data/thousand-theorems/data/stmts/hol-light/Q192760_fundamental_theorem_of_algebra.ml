(*
  Statement-only formalization of Thousand Theorems corpus artifact Q192760
  (thousand-theorems__hol-light__Q192760), "Fundamental theorem of algebra":
  every nonconstant polynomial over the complex numbers has a complex root.
  This file contains no proof.
*)

let Q192760_FUNDAMENTAL_THEOREM_OF_ALGEBRA =
  `let complex_zero = ((&0:real),(&0:real)) in
   let complex_add =
     \(x:real#real) (y:real#real).
       (FST x + FST y,SND x + SND y) in
   let complex_mul =
     \(x:real#real) (y:real#real).
       (FST x * FST y - SND x * SND y,
        FST x * SND y + SND x * FST y) in
   let polynomial_value =
     \(p:(real#real)list) (z:real#real).
       ITLIST
         (\a value. complex_add a (complex_mul z value))
         p complex_zero in
   !p:(real#real)list.
     (?u v:real#real. ~(polynomial_value p u = polynomial_value p v))
     ==> ?z:real#real. polynomial_value p z = complex_zero`;;
