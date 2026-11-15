(*
  Statement-only formalization of miniF2F valid problem
  algebra_xmysqpymzsqpzmxsqeqxyz_xpypzp6dvdx3y3z3. This file contains no proof.
*)

let statement =
  `!x y z:int.
     (x - y) pow 2 + (y - z) pow 2 + (z - x) pow 2 = x * y * z
     ==> (x + y + z + &6) divides
         (x pow 3 + y pow 3 + z pow 3)`;;
