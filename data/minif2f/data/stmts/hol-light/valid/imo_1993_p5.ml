(*
  Statement-only formalization of miniF2F valid problem imo_1993_p5. This file contains no
  proof.
*)

(*
  miniF2F valid artifact imo_1993_p5: existence of a strictly increasing
  function on the natural numbers with f 1 = 2 and f (f n) = f n + n.
  This is a statement-only formalization and contains no proof.
*)

let imo_1993_p5 =
  `?f:num->num.
     (!a b:num. (a < b <=> f a < f b)) /\
     f 1 = 2 /\
     (!n:num. f (f n) = f n + n)`;;
