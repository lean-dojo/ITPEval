(* Statement-only formalization of the Fundamental Theorem of Algebra. *)

needs "Complex/cpoly.ml";;

let FUNDAMENTAL_THEOREM_OF_ALGEBRA =
  `!p. ~constant(poly p) ==> ?z. poly p z = Cx(&0)`;;
