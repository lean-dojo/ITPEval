(*
  Statement-only formalization of miniF2F test problem numbertheory_notEquiv2i2jasqbsqdiv8. This
  file contains no proof.
*)

let statement =
  `~(!a b:int.
      ((?i j:int. a = &2 * i /\ b = &2 * j) <=>
       (?k:int. a pow 2 + b pow 2 = &8 * k)))`;;
