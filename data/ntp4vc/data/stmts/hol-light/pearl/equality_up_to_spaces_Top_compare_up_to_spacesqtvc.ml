(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/equality_up_to_spaces_Top_compare_up_to_spacesqtvc: a verification
  condition for comparing two character lists after recursively removing
  occurrences of a distinguished space character. This file contains no proof.
*)

let ntp4vc_compare_spaces_drop =
  new_recursive_definition num_RECURSION
   `(!xs:A list. ntp4vc_compare_spaces_drop 0 xs = xs) /\
    (!n:num.
     !xs:A list.
       ntp4vc_compare_spaces_drop (SUC n) xs =
       if xs = [] then []
       else ntp4vc_compare_spaces_drop n (TL xs))`;;

let statement =
 `!space:A.
  !eq:A->A->bool.
  !remove_spaces:A list->A list.
    (!u v:A. (eq u v = T <=> u = v))
    ==>
    (!s:A list.
       if (&(LENGTH s):int) = (&0:int) then
         remove_spaces s = s
       else if eq (EL 0 s) space = T then
         remove_spaces s = remove_spaces (ntp4vc_compare_spaces_drop 1 s)
       else
         remove_spaces s =
           CONS
             (EL 0 s)
             (remove_spaces (ntp4vc_compare_spaces_drop 1 s)))
    ==>
    !x y:A list.
      let n = (&(LENGTH x):int) in
      let m = (&(LENGTH y):int) in
      (((&0:int) <= (&0:int) /\ (&0:int) <= n) /\
       ((&0:int) <= (&0:int) /\ (&0:int) <= m) /\
       (remove_spaces x = remove_spaces y <=>
        remove_spaces (ntp4vc_compare_spaces_drop 0 x) =
        remove_spaces (ntp4vc_compare_spaces_drop 0 y))) /\
      (!j i:int.
         (((&0:int) <= i /\ i <= n) /\
          ((&0:int) <= j /\ j <= m) /\
          (remove_spaces x = remove_spaces y <=>
           remove_spaces (ntp4vc_compare_spaces_drop (num_of_int i) x) =
           remove_spaces (ntp4vc_compare_spaces_drop (num_of_int j) y)))
         ==>
         (!o1:bool.
            (if i < n then
               o1 = T
             else
               o1 = (if j < m then T else F))
            ==>
            (if o1 = T then
               !o2:bool.
                 (if i < n then
                    let o3 = space in
                    let o4 = EL (num_of_int i) x in
                    o2 = eq o4 o3 /\
                    (o2 = T <=> o4 = o3)
                  else
                    o2 = F)
                 ==>
                 (if o2 = T then
                    ((&0:int) <= n - i + m - j /\
                     n - (i + (&1:int)) + m - j <
                       n - i + m - j) /\
                    ((&0:int) <= i + (&1:int) /\
                     i + (&1:int) <= n) /\
                    ((&0:int) <= j /\ j <= m) /\
                    (remove_spaces x = remove_spaces y <=>
                     remove_spaces
                       (ntp4vc_compare_spaces_drop
                         (num_of_int (i + (&1:int))) x) =
                     remove_spaces
                       (ntp4vc_compare_spaces_drop (num_of_int j) y))
                  else
                    !o3:bool.
                      (if j < m then
                         let o4 = space in
                         let o5 = EL (num_of_int j) y in
                         o3 = eq o5 o4 /\
                         (o3 = T <=> o5 = o4)
                       else
                         o3 = F)
                      ==>
                      (if o3 = T then
                         ((&0:int) <= n - i + m - j /\
                          n - i + m - (j + (&1:int)) <
                            n - i + m - j) /\
                         ((&0:int) <= i /\ i <= n) /\
                         ((&0:int) <= j + (&1:int) /\
                          j + (&1:int) <= m) /\
                         (remove_spaces x = remove_spaces y <=>
                          remove_spaces
                            (ntp4vc_compare_spaces_drop
                              (num_of_int i) x) =
                          remove_spaces
                            (ntp4vc_compare_spaces_drop
                              (num_of_int (j + (&1:int))) y))
                       else
                         !o4:bool.
                           (if i = n then
                              o4 = T
                            else
                              o4 = (if j = m then T else F))
                           ==>
                           (if o4 = T then
                              ~(remove_spaces x = remove_spaces y)
                            else
                              let o5 = EL (num_of_int j) y in
                              let o6 = EL (num_of_int i) x in
                              let o7 = eq o6 o5 in
                              (o7 = T <=> o6 = o5)
                              ==>
                              (if ~(o7 = T) then
                                 ~(remove_spaces x = remove_spaces y)
                               else
                                 ((&0:int) <= n - i + m - j /\
                                  n - (i + (&1:int)) +
                                    m - (j + (&1:int)) <
                                    n - i + m - j) /\
                                 ((&0:int) <= i + (&1:int) /\
                                  i + (&1:int) <= n) /\
                                 ((&0:int) <= j + (&1:int) /\
                                  j + (&1:int) <= m) /\
                                 (remove_spaces x = remove_spaces y <=>
                                  remove_spaces
                                    (ntp4vc_compare_spaces_drop
                                      (num_of_int (i + (&1:int))) x) =
                                  remove_spaces
                                    (ntp4vc_compare_spaces_drop
                                      (num_of_int (j + (&1:int))) y))))))
             else
               remove_spaces x = remove_spaces y)))`;;
