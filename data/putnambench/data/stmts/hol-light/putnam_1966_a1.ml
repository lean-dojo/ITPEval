(*
  Statement-only formalization of PutnamBench artifact putnam_1966_a1:
  the inclusive partial-sum identity for the integer sequence whose m-th
  term is m / 2 when m is even and (m - 1) / 2 when m is odd.
  This file contains no proof.
*)

let statement =
  `!f:int->int.
     f =
     (\n:int.
        iterate (+) {m:int | &0 <= m /\ m <= n}
                    (\m. if m rem &2 = &0
                         then m div &2
                         else (m - &1) div &2))
     ==> !x y:int.
           &0 < x /\ &0 < y /\ y < x
           ==> x * y = f (x + y) - f (x - y)`;;
