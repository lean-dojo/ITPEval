(*
  Statement-only formalization of Thousand Theorems corpus artifact Q853067,
  "Solutions to Pell's equation": every natural-number solution of
  x^2 - (a^2 - 1)y^2 = 1 for a > 1 occurs in the recursively generated Pell
  sequence starting at (1,0). This file contains no proof.
*)

let q853067_pell_pair = new_recursive_definition num_RECURSION
  `(q853067_pell_pair a 0 = (1,0)) /\
   (!n. q853067_pell_pair a (SUC n) =
        (FST (q853067_pell_pair a n) * a +
           (a * a - 1) * SND (q853067_pell_pair a n),
         FST (q853067_pell_pair a n) +
           SND (q853067_pell_pair a n) * a))`;;

let q853067_pell_x = new_definition
  `q853067_pell_x a n = FST (q853067_pell_pair a n)`;;

let q853067_pell_y = new_definition
  `q853067_pell_y a n = SND (q853067_pell_pair a n)`;;

let Q853067_SOLUTIONS_TO_PELLS_EQUATION =
  `!a x y:num.
     1 < a
     ==> x * x - (a * a - 1) * y * y = 1
     ==> ?n:num.
           x = q853067_pell_x a n /\
           y = q853067_pell_y a n`;;
