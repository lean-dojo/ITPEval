(*
  Statement-only formalization of PutnamBench artifact putnam_1977_a1:
  four distinct points on the quartic y = 2x^4 + 7x^3 + 3x - 5 that lie on
  one line have average x-coordinate -7/8. This file contains no proof.
*)

let statement =
  `let f =
     \x:real. &2 * x pow 4 + &7 * x pow 3 + &3 * x - &5 in
   !S:real->bool.
     S HAS_SIZE 4 /\
     (?m b:real. !x:real. x IN S ==> f x = m * x + b)
     ==> sum S (\x:real. x) / &4 = --(&7 / &8)`;;
