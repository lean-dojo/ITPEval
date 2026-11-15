(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sf_HoareLogic_parityqtvc: the parity-loop verification condition over
  unbounded integers, with inductively generated evenness, invariant
  initialization, decrement preservation, and exit characterization. This
  file contains no proof.
*)

let sf_hoarelogic_even_RULES,
    sf_hoarelogic_even_INDUCT,
    sf_hoarelogic_even_CASES =
  new_inductive_definition
   `(sf_hoarelogic_even (&0:int)) /\
    (!z:int.
       sf_hoarelogic_even z
       ==> sf_hoarelogic_even (z + (&2:int)))`;;

let statement =
 `!x:int.
    (&0:int) <= x
    ==>
    (&0:int) <= x /\
    (sf_hoarelogic_even (x - x) \/
     ((&0:int) = (&1:int) /\
      sf_hoarelogic_even (x - x + (&1:int)))) /\
    (!y x1:int.
       (&0:int) <= x1 /\
       ((y = (&0:int) /\ sf_hoarelogic_even (x - x1)) \/
        (y = (&1:int) /\
         sf_hoarelogic_even (x - x1 + (&1:int))))
       ==>
       if ~(x1 = (&0:int)) then
         ((&0:int) <= x1 /\ x1 - (&1:int) < x1) /\
         (&0:int) <= x1 - (&1:int) /\
         (((&1:int) - y = (&0:int) /\
           sf_hoarelogic_even (x - (x1 - (&1:int)))) \/
          ((&1:int) - y = (&1:int) /\
           sf_hoarelogic_even
             (x - (x1 - (&1:int)) + (&1:int))))
       else
         ((y = (&0:int)) <=> sf_hoarelogic_even x))`;;
