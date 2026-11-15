(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sf_HoareLogic_factorialqtvc: the factorial-loop verification
  condition over unbounded integers, using the zero value and positive
  recurrence laws for factorial. This file contains no proof.
*)

let statement =
  `!fact:int->int.
     fact (&0:int) = (&1:int)
     ==> (!n:int.
            (&0:int) < n
            ==> fact n = n * fact (n - (&1:int)))
     ==> !x:int.
           (&0:int) <= x
           ==> (&0:int) <= x /\
               (&1:int) * fact x = fact x /\
               (!z y:int.
                  (&0:int) <= z /\ y * fact z = fact x
                  ==> if ~(z = (&0:int)) then
                        ((&0:int) <= z /\ z - (&1:int) < z) /\
                        (&0:int) <= z - (&1:int) /\
                        y * z * fact (z - (&1:int)) = fact x
                      else
                        y = fact x)`;;
