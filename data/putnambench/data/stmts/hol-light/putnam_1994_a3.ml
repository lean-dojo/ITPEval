(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1994_a3:
  four-coloring the full unit isosceles right triangle forces two same-colored
  points at distance at least 2 - sqrt 2. This file contains no proof.
*)

let statement =
  `let triangle =
     {p:real^2 |
        &0 <= p$1 /\ &0 <= p$2 /\ p$1 + p$2 <= &1} in
   let edist =
     \(p:real^2) (q:real^2).
       sqrt ((p$1 - q$1) pow 2 + (p$2 - q$2) pow 2) in
   !Tcolors:real^2->4.
     ?p q:real^2.
       p IN triangle /\
       q IN triangle /\
       Tcolors p = Tcolors q /\
       edist p q >= &2 - sqrt(&2)`;;
