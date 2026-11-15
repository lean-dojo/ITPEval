(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2019_ghc_sort_Top_sorted_listsqtvc: the recursive
  verification condition for turning monotonic array segments delimited by
  ordered cutpoints into nondecreasing integer lists while preserving all
  occurrence counts across the covered interval. This file contains no proof.
*)

let ntp4vc_sorted_lists_to_num = new_definition
 `ntp4vc_sorted_lists_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let ntp4vc_sorted_lists_nth = new_definition
 `ntp4vc_sorted_lists_nth (l:int list) (i:int) =
    if ntp4vc_sorted_lists_to_num i < LENGTH l then
      EL (ntp4vc_sorted_lists_to_num i) l
    else
      (&0:int)`;;

let ntp4vc_sorted_lists_take =
  new_recursive_definition num_RECURSION
   `(!l:int list.
       ntp4vc_sorted_lists_take 0 l = []) /\
    (!n:num.
     !l:int list.
       ntp4vc_sorted_lists_take (SUC n) l =
       if l = [] then []
       else CONS (HD l) (ntp4vc_sorted_lists_take n (TL l)))`;;

let ntp4vc_sorted_lists_count = new_definition
 `ntp4vc_sorted_lists_count (x:int) (l:int list) =
    (&(CARD
       {k:num | k < LENGTH l /\ EL k l = x}):int)`;;

let ntp4vc_sorted_lists_flatten =
  new_recursive_definition list_RECURSION
   `(ntp4vc_sorted_lists_flatten ([]:(int list)list) =
       ([]:int list)) /\
    (!h:int list.
     !t:(int list)list.
       ntp4vc_sorted_lists_flatten (CONS h t) =
       APPEND h (ntp4vc_sorted_lists_flatten t))`;;

let ntp4vc_sorted_lists_permut = new_definition
 `ntp4vc_sorted_lists_permut (left:int list) (right:int list) <=>
    LENGTH left = LENGTH right /\
    (!x:int.
       ntp4vc_sorted_lists_count x left =
       ntp4vc_sorted_lists_count x right)`;;

let ntp4vc_sorted_lists_map_occ = new_definition
 `ntp4vc_sorted_lists_map_occ
    (x:int) (s:int list) (lo:int) (hi:int) =
    (&(CARD
       {k:int |
          lo <= k /\ k < hi /\ ntp4vc_sorted_lists_nth s k = x}):int)`;;

let ntp4vc_sorted_lists_sorted =
  new_recursive_definition list_RECURSION
   `(!r:int->int->bool.
       ntp4vc_sorted_lists_sorted r ([]:int list) <=> T) /\
    (!r:int->int->bool.
     !h:int.
     !t:int list.
       ntp4vc_sorted_lists_sorted r (CONS h t) <=>
       (t = [] \/
        (r h (HD t) /\ ntp4vc_sorted_lists_sorted r t)))`;;

let ntp4vc_sorted_lists_strict = new_definition
 `ntp4vc_sorted_lists_strict (l:int list) <=>
    ntp4vc_sorted_lists_sorted (\x y:int. x < y) l`;;

let ntp4vc_sorted_lists_increasing = new_definition
 `ntp4vc_sorted_lists_increasing (l:int list) <=>
    ntp4vc_sorted_lists_sorted (\x y:int. x <= y) l`;;

let ntp4vc_sorted_lists_decreasing = new_definition
 `ntp4vc_sorted_lists_decreasing (l:int list) <=>
    ntp4vc_sorted_lists_sorted (\x y:int. y <= x) l`;;

let ntp4vc_sorted_lists_strict_segment = new_definition
 `ntp4vc_sorted_lists_strict_segment
    (s:int list) (lo:int) (hi:int) <=>
    !z1 z2:int.
      lo <= z1 /\ z1 < z2 /\ z2 < hi
      ==> ntp4vc_sorted_lists_nth s z1 <
          ntp4vc_sorted_lists_nth s z2`;;

let ntp4vc_sorted_lists_decreasing_segment = new_definition
 `ntp4vc_sorted_lists_decreasing_segment
    (s:int list) (lo:int) (hi:int) <=>
    !z1 z2:int.
      lo <= z1 /\ z1 < z2 /\ z2 < hi
      ==> ntp4vc_sorted_lists_nth s z2 <=
          ntp4vc_sorted_lists_nth s z1`;;

let ntp4vc_sorted_lists_precondition = new_definition
 `ntp4vc_sorted_lists_precondition
    (list_of:A->int list)
    (seq_of:A->int list)
    (s:int list)
    (cutp:A) <=>
    (&0:int) < (&(LENGTH (list_of cutp)):int) /\
    (!x y:int.
       (&0:int) <= x /\
       x < y /\
       y < (&(LENGTH (seq_of cutp)):int)
       ==> ntp4vc_sorted_lists_nth (seq_of cutp) x <=
           ntp4vc_sorted_lists_nth (seq_of cutp) y) /\
    (!z:int.
       MEM z (list_of cutp)
       ==> (&0:int) <= z /\ z <= (&(LENGTH s):int)) /\
    (!k:int.
       (&0:int) <= k /\
       k < (&(LENGTH (seq_of cutp)):int) - (&1:int)
       ==> let ck = ntp4vc_sorted_lists_nth (seq_of cutp) k in
           let ck1 =
             ntp4vc_sorted_lists_nth (seq_of cutp) (k + (&1:int)) in
           ntp4vc_sorted_lists_strict_segment s ck ck1 \/
           ntp4vc_sorted_lists_decreasing_segment s ck ck1)`;;

let ntp4vc_sorted_lists_segment_spec = new_definition
 `ntp4vc_sorted_lists_segment_spec
    (s:int list) (lo:int) (hi:int) (seqi:int list) <=>
    (!x:int.
       ntp4vc_sorted_lists_count x seqi =
       ntp4vc_sorted_lists_map_occ x s lo hi) /\
    (!x:int.
       MEM x seqi
       ==> ?z:int.
             (lo <= z /\ z < hi) /\
             ntp4vc_sorted_lists_nth s z = x) /\
    (ntp4vc_sorted_lists_strict_segment s lo hi
     ==> ntp4vc_sorted_lists_strict seqi) /\
    (ntp4vc_sorted_lists_decreasing_segment s lo hi
     ==> ntp4vc_sorted_lists_decreasing seqi) /\
    (ntp4vc_sorted_lists_strict seqi \/
     ntp4vc_sorted_lists_decreasing seqi)`;;

let ntp4vc_sorted_lists_slice_spec = new_definition
 `ntp4vc_sorted_lists_slice_spec
    (whole:int list) (upper:int) (part:int list) <=>
    (&(LENGTH part):int) = upper - (&0:int) /\
    (!k:int.
       (&0:int) <= k /\ k < upper - (&0:int)
       ==> ntp4vc_sorted_lists_nth part k =
           ntp4vc_sorted_lists_nth whole ((&0:int) + k))`;;

let ntp4vc_sorted_lists_result_spec = new_definition
 `ntp4vc_sorted_lists_result_spec
    (s:int list) (cutseq:int list) (result:(int list)list) <=>
    (!l:int list.
       MEM l result ==> ntp4vc_sorted_lists_increasing l) /\
    (!x:int.
       ntp4vc_sorted_lists_count
         x (ntp4vc_sorted_lists_flatten result) =
       ntp4vc_sorted_lists_map_occ
         x
         s
         (ntp4vc_sorted_lists_nth cutseq (&0:int))
         (ntp4vc_sorted_lists_nth
            cutseq
            ((&(LENGTH cutseq):int) - (&1:int))))`;;

let ntp4vc_sorted_lists_recursive_obligation = new_definition
 `ntp4vc_sorted_lists_recursive_obligation
    (list_of:A->int list)
    (seq_of:A->int list)
    (s:int list)
    (cutp:A) <=>
    let ls = list_of cutp in
    let seq1 = seq_of cutp in
    if ls = [] then T
    else if TL ls = [] then T
    else
      let h1 = HD ls in
      let h2 = HD (TL ls) in
      let t = TL (TL ls) in
      (((&0:int) <= h2 /\ h2 <= (&(LENGTH s):int)) /\
       ((&0:int) <= h1 /\ h1 <= (&(LENGTH s):int)) /\
       (ntp4vc_sorted_lists_strict_segment s h2 h1 \/
        ntp4vc_sorted_lists_decreasing_segment s h2 h1)) /\
      (!seqi:int list.
         ntp4vc_sorted_lists_segment_spec s h2 h1 seqi
         ==>
         (let o1 = (&(LENGTH seq1):int) - (&1:int) in
          (((&0:int) <= (&0:int) /\
            (&0:int) <= o1 /\
           o1 <= (&(LENGTH seq1):int)) /\
           (let o2 =
              ntp4vc_sorted_lists_take
                (ntp4vc_sorted_lists_to_num o1) seq1 in
            ntp4vc_sorted_lists_slice_spec seq1 o1 o2
            ==>
            (let o3 = CONS h2 t in
             o2 = REVERSE o3 /\
             (!lseq:A.
                list_of lseq = o3 /\ seq_of lseq = o2
                ==>
                (((if list_of cutp = [] then F
                   else TL (list_of cutp) = list_of lseq) /\
                  ntp4vc_sorted_lists_precondition
                    list_of seq_of s lseq) /\
                 (!o4:(int list)list.
                    ntp4vc_sorted_lists_result_spec
                      s (seq_of lseq) o4
                    ==>
                    ntp4vc_sorted_lists_strict seqi \/
                    ntp4vc_sorted_lists_decreasing seqi))))))))`;;

let ntp4vc_sorted_lists_result_obligation = new_definition
 `ntp4vc_sorted_lists_result_obligation
    (list_of:A->int list)
    (seq_of:A->int list)
    (order:int list->int list)
    (s:int list)
    (cutp:A) <=>
    let ls = list_of cutp in
    let seq1 = seq_of cutp in
    !result:(int list)list.
      (if ls = [] then
         result = []
       else if TL ls = [] then
         result = []
       else
         let h1 = HD ls in
         let h2 = HD (TL ls) in
         let t = TL (TL ls) in
         ?seqi:int list.
           ntp4vc_sorted_lists_segment_spec s h2 h1 seqi /\
           (let o1 = (&(LENGTH seq1):int) - (&1:int) in
            let o2 =
              ntp4vc_sorted_lists_take
                (ntp4vc_sorted_lists_to_num o1) seq1 in
            ntp4vc_sorted_lists_slice_spec seq1 o1 o2 /\
            (?lseq:A.
               (list_of lseq = CONS h2 t /\ seq_of lseq = o2) /\
               (?o3:(int list)list.
                  ntp4vc_sorted_lists_result_spec
                    s (seq_of lseq) o3 /\
                  (let o4 = order seqi in
                   (ntp4vc_sorted_lists_increasing o4 /\
                    ntp4vc_sorted_lists_permut seqi o4) /\
                   result = CONS o4 o3)))))
      ==>
      ntp4vc_sorted_lists_result_spec s (seq_of cutp) result`;;

let statement =
 `!list_of seq_of:A->int list.
  !order:int list->int list.
  !cutp:A.
  !s:int list.
    (!self:A. seq_of self = REVERSE (list_of self))
    ==>
    (!a b:A.
       list_of a = list_of b /\ seq_of a = seq_of b
       ==> a = b)
    ==>
    (!l:int list.
       ?a:A.
         list_of a = l /\ seq_of a = REVERSE l)
    ==>
    (!l:int list.
       ntp4vc_sorted_lists_strict l \/
       ntp4vc_sorted_lists_decreasing l
       ==>
       order l =
       if l = [] then l
       else if TL l = [] then l
       else if HD l < HD (TL l) then l
       else REVERSE l)
    ==>
    (!l:int list.
       ntp4vc_sorted_lists_strict l \/
       ntp4vc_sorted_lists_decreasing l
       ==> ntp4vc_sorted_lists_increasing (order l))
    ==>
    (!l:int list.
       ntp4vc_sorted_lists_strict l \/
       ntp4vc_sorted_lists_decreasing l
       ==> ntp4vc_sorted_lists_permut l (order l))
    ==>
    ntp4vc_sorted_lists_precondition list_of seq_of s cutp
    ==>
    ntp4vc_sorted_lists_recursive_obligation list_of seq_of s cutp /\
    ntp4vc_sorted_lists_result_obligation
      list_of seq_of order s cutp`;;
