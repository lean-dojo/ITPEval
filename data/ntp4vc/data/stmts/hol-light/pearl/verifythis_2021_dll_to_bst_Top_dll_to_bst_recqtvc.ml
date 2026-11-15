(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_dll_to_bst_Top_dll_to_bst_recqtvc: the recursive
  doubly-linked-list to balanced binary-search-tree verification condition,
  preserving finite-map domains and out-of-segment links while establishing
  the tree relation and logarithmic height bound. This file contains no proof.
*)

let ntp4vc_dll_bst_tree_INDUCT,
    ntp4vc_dll_bst_tree_RECURSION =
  define_type
    "ntp4vc_dll_bst_tree =
       NTP4VCDllBstEmpty
     | NTP4VCDllBstNode
         ntp4vc_dll_bst_tree int ntp4vc_dll_bst_tree";;

let ntp4vc_dll_bst_int_index = new_definition
 `ntp4vc_dll_bst_int_index (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let ntp4vc_dll_bst_nth = new_definition
 `ntp4vc_dll_bst_nth (xs:A list) (i:int) =
    if ntp4vc_dll_bst_int_index i < LENGTH xs
    then EL (ntp4vc_dll_bst_int_index i) xs
    else ARB`;;

let ntp4vc_dll_bst_fmap_domain = new_definition
 `ntp4vc_dll_bst_fmap_domain (m:A->B option) =
    {key:A | ?value:B. m key = SOME value}`;;

let ntp4vc_dll_bst_fmap_lookup = new_definition
 `ntp4vc_dll_bst_fmap_lookup (key:A) (m:A->B option) =
    @value:B. m key = SOME value`;;

let ntp4vc_dll_bst_option_the = new_definition
 `ntp4vc_dll_bst_option_the (value:A option) =
    @x:A. value = SOME x`;;

let ntp4vc_dll_bst_fmap_update = new_definition
 `ntp4vc_dll_bst_fmap_update
    (key:A) (value:B) (m:A->B option) =
    \other:A. if other = key then SOME value else m other`;;

let ntp4vc_dll_bst_valid = new_definition
 `ntp4vc_dll_bst_valid
    (null:A)
    (prev:A->A option)
    (next:A->A option)
    (s:A list) <=>
    !i:int.
      (&0:int) <= i /\ i < (&(LENGTH s):int)
      ==>
      ~(ntp4vc_dll_bst_nth s i = null) /\
      ntp4vc_dll_bst_nth s i IN
        ntp4vc_dll_bst_fmap_domain prev /\
      ntp4vc_dll_bst_nth s i IN
        ntp4vc_dll_bst_fmap_domain next /\
      (!j:int.
         i < j /\ j < (&(LENGTH s):int)
         ==> ~(ntp4vc_dll_bst_nth s i =
               ntp4vc_dll_bst_nth s j))`;;

let ntp4vc_dll_bst_dll = new_definition
 `ntp4vc_dll_bst_dll
    (null:A)
    (prev:A->A option)
    (next:A->A option)
    (s:A list)
    (head:A)
    (lo:int)
    (hi:int) <=>
    ntp4vc_dll_bst_valid null prev next s /\
    (&0:int) <= lo /\ lo <= hi /\ hi <= (&(LENGTH s):int) /\
    head =
      (if lo = (&(LENGTH s):int)
       then null
       else ntp4vc_dll_bst_nth s lo) /\
    (!i:int.
       lo <= i /\ i < hi - (&1:int)
       ==>
       ntp4vc_dll_bst_fmap_lookup
         (ntp4vc_dll_bst_nth s i) next =
       ntp4vc_dll_bst_nth s (i + (&1:int))) /\
    (!i:int.
       lo < i /\ i < hi
       ==>
       ntp4vc_dll_bst_fmap_lookup
         (ntp4vc_dll_bst_nth s i) prev =
       ntp4vc_dll_bst_nth s (i - (&1:int))) /\
    (lo < hi
     ==>
     ntp4vc_dll_bst_fmap_lookup
       (ntp4vc_dll_bst_nth s (hi - (&1:int))) next =
     (if hi = (&(LENGTH s):int)
      then null
      else ntp4vc_dll_bst_nth s hi)) /\
    (lo < hi
     ==>
     ntp4vc_dll_bst_fmap_lookup
       (ntp4vc_dll_bst_nth s lo) prev =
     (if lo = (&0:int)
      then null
      else ntp4vc_dll_bst_nth s (lo - (&1:int))))`;;

let ntp4vc_dll_bst_tree =
  new_recursive_definition ntp4vc_dll_bst_tree_RECURSION
   `(!null:A.
     !prev next:A->A option.
     !s:A list.
     !root:A.
     !lo hi:int.
       ntp4vc_dll_bst_tree
         null prev next s root NTP4VCDllBstEmpty lo hi <=>
       ntp4vc_dll_bst_valid null prev next s /\
       (&0:int) <= lo /\ lo <= hi /\ hi <= (&(LENGTH s):int) /\
       root = null /\ lo = hi) /\
    (!null:A.
     !prev next:A->A option.
     !s:A list.
     !root:A.
     !left right:ntp4vc_dll_bst_tree.
     !position lo hi:int.
       ntp4vc_dll_bst_tree
         null prev next s root
         (NTP4VCDllBstNode left position right) lo hi <=>
       ntp4vc_dll_bst_valid null prev next s /\
       (&0:int) <= lo /\ lo <= hi /\ hi <= (&(LENGTH s):int) /\
       lo <= position /\ position < hi /\
       root = ntp4vc_dll_bst_nth s position /\
       ntp4vc_dll_bst_tree
         null prev next s
         (ntp4vc_dll_bst_fmap_lookup root prev)
         left lo position /\
       ntp4vc_dll_bst_tree
         null prev next s
         (ntp4vc_dll_bst_fmap_lookup root next)
         right (position + (&1:int)) hi)`;;

let ntp4vc_dll_bst_int_max = new_definition
 `ntp4vc_dll_bst_int_max (x:int) (y:int) =
    if x <= y then y else x`;;

let ntp4vc_dll_bst_height =
  new_recursive_definition ntp4vc_dll_bst_tree_RECURSION
   `(ntp4vc_dll_bst_height NTP4VCDllBstEmpty = (&0:int)) /\
    (!left right:ntp4vc_dll_bst_tree.
     !position:int.
       ntp4vc_dll_bst_height
         (NTP4VCDllBstNode left position right) =
       (&1:int) +
       ntp4vc_dll_bst_int_max
         (ntp4vc_dll_bst_height left)
         (ntp4vc_dll_bst_height right))`;;

let ntp4vc_dll_bst_int_power = new_definition
 `ntp4vc_dll_bst_int_power (base:int) (exponent:int) =
    base pow
      (if exponent < (&0:int) then 0 else num_of_int exponent)`;;

let ntp4vc_dll_bst_int_div2 = new_definition
 `ntp4vc_dll_bst_int_div2 (n:int) =
    if (&0:int) <= n
    then (&(num_of_int n DIV 2):int)
    else --(&(num_of_int (--n) DIV 2):int)`;;

let statement =
 `!to_fmap:A->B->B option.
  !null:B.
  !prev next:A.
  !s:B list.
  !head:B.
  !ihead n:int.
    (!container:A.
       FINITE (ntp4vc_dll_bst_fmap_domain (to_fmap container)))
    ==>
    ntp4vc_dll_bst_dll
      null (to_fmap prev) (to_fmap next) s head
      ihead (ihead + n)
    ==>
    (if n = (&0:int) then
       head =
         (if ihead + n = (&(LENGTH s):int)
          then null
          else ntp4vc_dll_bst_nth s (ihead + n)) /\
       ntp4vc_dll_bst_tree
         null (to_fmap prev) (to_fmap next) s null
         NTP4VCDllBstEmpty ihead (ihead + n) /\
       ntp4vc_dll_bst_fmap_domain (to_fmap prev) =
         ntp4vc_dll_bst_fmap_domain (to_fmap prev) /\
       ntp4vc_dll_bst_fmap_domain (to_fmap next) =
         ntp4vc_dll_bst_fmap_domain (to_fmap next) /\
       ((&0:int) < n
        ==>
        (let h = ntp4vc_dll_bst_height NTP4VCDllBstEmpty in
         ntp4vc_dll_bst_int_power (&2:int) (h - (&1:int)) <= n /\
         n < ntp4vc_dll_bst_int_power (&2:int) h))
     else
       ~((&2:int) = (&0:int)) /\
       (let nl = ntp4vc_dll_bst_int_div2 n in
        let pivot =
          if ihead + nl = (&(LENGTH s):int)
          then null
          else ntp4vc_dll_bst_nth s (ihead + nl) in
        (((&0:int) <= n /\ nl < n) /\
         ntp4vc_dll_bst_dll
           null (to_fmap prev) (to_fmap next) s head
           ihead (ihead + nl)) /\
        (!next1 prev1:A.
         !left1:B.
         !left_tree:ntp4vc_dll_bst_tree.
           (ntp4vc_dll_bst_tree
              null (to_fmap prev1) (to_fmap next1) s
              left1 left_tree ihead (ihead + nl) /\
            ntp4vc_dll_bst_fmap_domain (to_fmap prev1) =
              ntp4vc_dll_bst_fmap_domain (to_fmap prev) /\
            ntp4vc_dll_bst_fmap_domain (to_fmap next1) =
              ntp4vc_dll_bst_fmap_domain (to_fmap next) /\
            (!i:int.
               (&0:int) <= i /\ i < ihead
               ==>
               ntp4vc_dll_bst_fmap_lookup
                 (ntp4vc_dll_bst_nth s i) (to_fmap prev1) =
               ntp4vc_dll_bst_fmap_lookup
                 (ntp4vc_dll_bst_nth s i) (to_fmap prev)) /\
            (!i:int.
               ihead + nl <= i /\ i < (&(LENGTH s):int)
               ==>
               ntp4vc_dll_bst_fmap_lookup
                 (ntp4vc_dll_bst_nth s i) (to_fmap prev1) =
               ntp4vc_dll_bst_fmap_lookup
                 (ntp4vc_dll_bst_nth s i) (to_fmap prev)) /\
            (!i:int.
               (&0:int) <= i /\ i < ihead
               ==>
               ntp4vc_dll_bst_fmap_lookup
                 (ntp4vc_dll_bst_nth s i) (to_fmap next1) =
               ntp4vc_dll_bst_fmap_lookup
                 (ntp4vc_dll_bst_nth s i) (to_fmap next)) /\
            (!i:int.
               ihead + nl <= i /\ i < (&(LENGTH s):int)
               ==>
               ntp4vc_dll_bst_fmap_lookup
                 (ntp4vc_dll_bst_nth s i) (to_fmap next1) =
               ntp4vc_dll_bst_fmap_lookup
                 (ntp4vc_dll_bst_nth s i) (to_fmap next)) /\
            ((&0:int) < nl
             ==>
             (let h = ntp4vc_dll_bst_height left_tree in
              ntp4vc_dll_bst_int_power
                (&2:int) (h - (&1:int)) <= nl /\
              nl < ntp4vc_dll_bst_int_power (&2:int) h)))
           ==>
           pivot IN ntp4vc_dll_bst_fmap_domain (to_fmap prev1) /\
           (!prev2:A.
              to_fmap prev2 =
                ntp4vc_dll_bst_fmap_update
                  pivot left1 (to_fmap prev1)
              ==>
              (let right_size = n - nl - (&1:int) in
               let right_start = ihead + nl + (&1:int) in
               pivot IN
                 ntp4vc_dll_bst_fmap_domain (to_fmap next1) /\
               (let right_head =
                  ntp4vc_dll_bst_fmap_lookup pivot (to_fmap next1) in
                right_head =
                  ntp4vc_dll_bst_option_the ((to_fmap next1) pivot)
                ==>
                (((&0:int) <= n /\ right_size < n) /\
                 ntp4vc_dll_bst_dll
                   null (to_fmap prev2) (to_fmap next1) s
                   right_head right_start (right_start + right_size)) /\
                (!next2 prev3:A.
                 !temp:B.
                 !right_tree:ntp4vc_dll_bst_tree.
                   (ntp4vc_dll_bst_tree
                      null (to_fmap prev3) (to_fmap next2) s
                      temp right_tree right_start
                      (right_start + right_size) /\
                    ntp4vc_dll_bst_fmap_domain (to_fmap prev3) =
                      ntp4vc_dll_bst_fmap_domain (to_fmap prev2) /\
                    ntp4vc_dll_bst_fmap_domain (to_fmap next2) =
                      ntp4vc_dll_bst_fmap_domain (to_fmap next1) /\
                    (!i:int.
                       (&0:int) <= i /\ i < right_start
                       ==>
                       ntp4vc_dll_bst_fmap_lookup
                         (ntp4vc_dll_bst_nth s i) (to_fmap prev3) =
                       ntp4vc_dll_bst_fmap_lookup
                         (ntp4vc_dll_bst_nth s i) (to_fmap prev2)) /\
                    (!i:int.
                       right_start + right_size <= i /\
                       i < (&(LENGTH s):int)
                       ==>
                       ntp4vc_dll_bst_fmap_lookup
                         (ntp4vc_dll_bst_nth s i) (to_fmap prev3) =
                       ntp4vc_dll_bst_fmap_lookup
                         (ntp4vc_dll_bst_nth s i) (to_fmap prev2)) /\
                    (!i:int.
                       (&0:int) <= i /\ i < right_start
                       ==>
                       ntp4vc_dll_bst_fmap_lookup
                         (ntp4vc_dll_bst_nth s i) (to_fmap next2) =
                       ntp4vc_dll_bst_fmap_lookup
                         (ntp4vc_dll_bst_nth s i) (to_fmap next1)) /\
                    (!i:int.
                       right_start + right_size <= i /\
                       i < (&(LENGTH s):int)
                       ==>
                       ntp4vc_dll_bst_fmap_lookup
                         (ntp4vc_dll_bst_nth s i) (to_fmap next2) =
                       ntp4vc_dll_bst_fmap_lookup
                         (ntp4vc_dll_bst_nth s i) (to_fmap next1)) /\
                    ((&0:int) < right_size
                     ==>
                     (let h = ntp4vc_dll_bst_height right_tree in
                      ntp4vc_dll_bst_int_power
                        (&2:int) (h - (&1:int)) <= right_size /\
                      right_size <
                        ntp4vc_dll_bst_int_power (&2:int) h)))
                   ==>
                   pivot IN
                     ntp4vc_dll_bst_fmap_domain (to_fmap next2) /\
                   (!next3:A.
                      to_fmap next3 =
                        ntp4vc_dll_bst_fmap_update
                          pivot temp (to_fmap next2)
                      ==>
                      (let whole_tree =
                         NTP4VCDllBstNode
                           left_tree (ihead + nl) right_tree in
                       (if right_start + right_size =
                           (&(LENGTH s):int)
                        then null
                        else
                          ntp4vc_dll_bst_nth
                            s (right_start + right_size)) =
                         (if ihead + n = (&(LENGTH s):int)
                          then null
                          else ntp4vc_dll_bst_nth s (ihead + n)) /\
                       ntp4vc_dll_bst_tree
                         null (to_fmap prev3) (to_fmap next3) s
                         pivot whole_tree ihead (ihead + n) /\
                       ntp4vc_dll_bst_fmap_domain (to_fmap prev3) =
                         ntp4vc_dll_bst_fmap_domain (to_fmap prev) /\
                       ntp4vc_dll_bst_fmap_domain (to_fmap next3) =
                         ntp4vc_dll_bst_fmap_domain (to_fmap next) /\
                       (!i:int.
                          (&0:int) <= i /\ i < ihead
                          ==>
                          ntp4vc_dll_bst_fmap_lookup
                            (ntp4vc_dll_bst_nth s i)
                            (to_fmap prev3) =
                          ntp4vc_dll_bst_fmap_lookup
                            (ntp4vc_dll_bst_nth s i)
                            (to_fmap prev)) /\
                       (!i:int.
                          ihead + n <= i /\ i < (&(LENGTH s):int)
                          ==>
                          ntp4vc_dll_bst_fmap_lookup
                            (ntp4vc_dll_bst_nth s i)
                            (to_fmap prev3) =
                          ntp4vc_dll_bst_fmap_lookup
                            (ntp4vc_dll_bst_nth s i)
                            (to_fmap prev)) /\
                       (!i:int.
                          (&0:int) <= i /\ i < ihead
                          ==>
                          ntp4vc_dll_bst_fmap_lookup
                            (ntp4vc_dll_bst_nth s i)
                            (to_fmap next3) =
                          ntp4vc_dll_bst_fmap_lookup
                            (ntp4vc_dll_bst_nth s i)
                            (to_fmap next)) /\
                       (!i:int.
                          ihead + n <= i /\ i < (&(LENGTH s):int)
                          ==>
                          ntp4vc_dll_bst_fmap_lookup
                            (ntp4vc_dll_bst_nth s i)
                            (to_fmap next3) =
                          ntp4vc_dll_bst_fmap_lookup
                            (ntp4vc_dll_bst_nth s i)
                            (to_fmap next)) /\
                       ((&0:int) < n
                        ==>
                        (let h =
                           ntp4vc_dll_bst_height whole_tree in
                         ntp4vc_dll_bst_int_power
                           (&2:int) (h - (&1:int)) <= n /\
                         n <
                           ntp4vc_dll_bst_int_power
                             (&2:int) h)))))))))))`;;
