(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sorted_list_FindInSortedList_findqtvc: the verification condition for
  recursively finding an integer in a sorted list, including the tail
  recursive-call obligation and equivalence of the Boolean result with list
  membership. This file contains no proof.
*)

let statement =
 `let sorted =
    \(l:int list).
      !i j:num.
        i < j /\ j < LENGTH l
        ==> EL i l <= EL j l in
  !l:int list. !x:int.
    sorted l
    ==>
    ((if l = [] then
        T
      else
        ~(x = HD l)
        ==>
        HD l < x
        ==>
        (if l = [] then F else TL l = TL l) /\ sorted (TL l)) /\
     (!result:bool.
        (if l = [] then
           result = F
         else if x = HD l then
           result = T
         else if HD l < x then
           result = (if MEM x (TL l) then T else F)
         else
           result = F)
        ==>
        (result = T <=> MEM x l)))`;;
