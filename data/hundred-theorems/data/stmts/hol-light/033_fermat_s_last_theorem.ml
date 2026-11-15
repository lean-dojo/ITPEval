(*
  Statement-only formalization of "Fermat's Last Theorem" from Hundred Theorems item 033. This
  file contains no proof.
*)

(* ========================================================================= *)
(* Fermat's Last Theorem.                                                    *)
(* ========================================================================= *)

let FERMAT_LAST_THEOREM =
  `!n:num.
      2 < n
      ==> ~(?a b c:num.
                0 < a /\ 0 < b /\ 0 < c /\
                a EXP n + b EXP n = c EXP n)`;;
