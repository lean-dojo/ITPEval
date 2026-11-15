(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/list_removal_Top_remove2qtvc: a linked-list removal verification
  condition for bypassing a distinguished entry by updating its predecessor's
  successor pointer. This file contains no proof.
*)

let ntp4vc_list_removal_function_update = new_definition
 `ntp4vc_list_removal_function_update
    (f:A->A) (x:A) (y:A) =
    \z:A. if z = x then y else f z`;;

let statement =
 `!null:A.
  !head:A.
  !entry:A.
  !list:(A->A)->A->int->A->bool.
    ~(head = null)
    ==>
    ~(entry = null)
    ==>
    ~(head = entry)
    ==>
    (!n:int.
     !mem1:A->A.
     !x:A.
     !y:A.
       (&0:int) <= n
       ==>
       if n = (&0:int) then
         (list mem1 x n y <=> x = y)
       else
         (list mem1 x n y <=>
          ~(x = null) /\ list mem1 (mem1 x) (n - (&1:int)) y))
    ==>
    !n1:int.
    !n2:int.
    !mem1:A->A.
      (&0:int) < n1
      ==>
      (&0:int) < n2
      ==>
      list mem1 head n1 entry
      ==>
      list mem1 entry n2 null
      ==>
      ((&0:int) < (&1:int) /\
       (&1:int) <= n1 /\
       ~(head = null) /\
       list mem1 head ((&1:int) - (&1:int)) head /\
       list mem1 (mem1 head) (n1 - (&1:int)) entry /\
       list mem1 entry n2 null /\
       (!n:int.
        !ind:A.
          (((&0:int) < n /\ n <= n1) /\
           ~(ind = null) /\
           list mem1 head (n - (&1:int)) ind /\
           list mem1 (mem1 ind) (n1 - n) entry /\
           list mem1 entry n2 null)
          ==>
          ~(ind = null) /\
          (if ~(mem1 ind = entry) then
             ~(ind = null) /\
             ((&0:int) <= n1 - n /\
              n1 - (n + (&1:int)) < n1 - n) /\
             ((&0:int) < n + (&1:int) /\
              n + (&1:int) <= n1) /\
             ~(mem1 ind = null) /\
             list mem1
               head (n + (&1:int) - (&1:int)) (mem1 ind) /\
             list mem1
               (mem1 (mem1 ind))
               (n1 - (n + (&1:int))) entry /\
             list mem1 entry n2 null
           else
             let o1 = entry in
             ~(o1 = null) /\
             ~(ind = null) /\
             list
               (ntp4vc_list_removal_function_update
                 mem1 ind (mem1 o1))
               head (n1 + n2 - (&1:int)) null)))`;;
