(*
  Statement-only formalization of "Euler's Generalization of Fermat's Little Theorem" from
  Hundred Theorems item 010. This file contains no proof.
*)

(* ========================================================================= *)
(* Euler's generalization of Fermat's little theorem.                        *)
(* ========================================================================= *)

needs "Library/pocklington.ml";;

prioritize_num();;

let EULER_GENERALIZATION_OF_FERMATS_LITTLE_THEOREM =
  `!a n. coprime(a,n) ==> (a EXP (phi n) == 1) (mod n)`;;
