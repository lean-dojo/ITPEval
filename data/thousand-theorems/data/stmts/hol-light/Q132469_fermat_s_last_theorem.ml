(*
  Statement-only formalization of Thousand Theorems corpus artifact Q132469,
  "Fermat's Last Theorem": for every natural exponent at least three, the
  Fermat equation has no solution in which all three natural numbers are
  nonzero. This file contains no proof.
*)

let Q132469_FERMAT_LAST_THEOREM =
  `!n:num.
     3 <= n
     ==> !a b c:num.
           ~(a = 0)
           ==> ~(b = 0)
           ==> ~(c = 0)
           ==> ~(a EXP n + b EXP n = c EXP n)`;;
