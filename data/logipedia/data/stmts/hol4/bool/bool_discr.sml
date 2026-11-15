(*
  Statement-only formalization of the Logipedia corpus artifact
  bool.bool_discr (catalog title "bool.bool_discr"): Boolean equality makes
  the corresponding nested Boolean case analysis select a universally valid
  proposition. This file contains no proof.
*)

open HolKernel Parse boolLib;

val bool_bool_discr =
  ``!(x : bool) (y : bool).
      x = y ==>
      (if x then
         if y then (!P : bool. P ==> P) else (!P : bool. P)
       else
         if y then (!P : bool. P) else (!P : bool. P ==> P))``;
