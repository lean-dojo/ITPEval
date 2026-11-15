(*
  Statement-only formalization of miniF2F valid problem imo_1973_p3. This file contains no
  proof.
*)

(*
  miniF2F valid artifact imo_1973_p3: if a real quartic
  x^4 + a*x^3 + b*x^2 + a*x + 1 has a real root, then
  4/5 <= a^2 + b^2. This is a statement-only formalization and contains no
  proof.
*)

let imo_1973_p3 =
  `!a b:real.
     (?x:real.
        x pow 4 + a * x pow 3 + b * x pow 2 + a * x + &1 = &0)
     ==> &4 / &5 <= a pow 2 + b pow 2`;;
