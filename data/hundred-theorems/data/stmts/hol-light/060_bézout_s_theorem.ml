(* Statement-only formalization of Bezout's theorem over the integers. *)

needs "Library/integer.ml";;

let BEZOUT_THEOREM =
  `!a b:int. ?d. &0 <= d /\ d divides a /\ d divides b /\
                    ?x y. d = a * x + b * y`;;
