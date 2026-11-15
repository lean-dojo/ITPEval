(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/list_removal_Top_remove1qtvc: a linked-list removal verification
  condition for unlinking a distinguished entry by updating either the head
  or its predecessor's successor pointer. This file contains no proof.
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
      let o1 = head in
      ~(o1 = null) /\
      (let o2 = mem1 o1 in
       (((&0:int) < (&1:int) /\ (&1:int) <= n1) /\
        list mem1 head (&1:int) o2 /\
        ~(o2 = null) /\
        list mem1 o2 (n1 - (&1:int)) entry /\
        list mem1 entry n2 null) /\
       (!n:int.
        !curr:A.
        !prev:A.
          (((&0:int) < n /\ n <= n1) /\
           list mem1 head n curr /\
           ~(curr = null) /\
           (prev = null ==> n = (&1:int)) /\
           (~(prev = null) ==> mem1 prev = curr) /\
           (~(prev = null) ==>
            list mem1 head (n - (&1:int)) prev) /\
           list mem1 curr (n1 - n) entry /\
           list mem1 entry n2 null)
          ==>
          if ~(curr = entry) then
            ~(curr = null) /\
            ((&0:int) <= n1 - n /\
             n1 - (n + (&1:int)) < n1 - n) /\
            ((&0:int) < n + (&1:int) /\
             n + (&1:int) <= n1) /\
            list mem1 head (n + (&1:int)) (mem1 curr) /\
            ~(mem1 curr = null) /\
            (curr = null ==> n + (&1:int) = (&1:int)) /\
            (~(curr = null) ==> T) /\
            (~(curr = null) ==>
             list mem1 head (n + (&1:int) - (&1:int)) curr) /\
            list mem1
              (mem1 curr) (n1 - (n + (&1:int))) entry /\
            list mem1 entry n2 null
          else if prev = null then
            ~(curr = null) /\
            (let o3 = head in
             ~(o3 = null) /\
             list
               (ntp4vc_list_removal_function_update
                 mem1 o3 (mem1 curr))
               head (n1 + n2 - (&1:int)) null)
          else
            ~(curr = null) /\
            ~(prev = null) /\
            list
              (ntp4vc_list_removal_function_update
                mem1 prev (mem1 curr))
              head (n1 + n2 - (&1:int)) null))`;;
