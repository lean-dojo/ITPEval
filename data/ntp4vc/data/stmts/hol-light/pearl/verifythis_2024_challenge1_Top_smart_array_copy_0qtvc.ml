(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2024_challenge1_Top_smart_array_copy_0qtvc: the
  verification condition for smart array copying by shuffled subsegments,
  including permutation pairs, nested element-copy loop invariants, and
  extensional list-update conditions. This file contains no proof.
*)

let ntp4vc_sac0_nth_int = new_definition
 `ntp4vc_sac0_nth_int (a:int list) (i:int) =
    if i < (&0:int) then (&0:int)
    else if num_of_int i < LENGTH a
         then EL (num_of_int i) a
         else (&0:int)`;;

let ntp4vc_sac0_nth = new_definition
 `ntp4vc_sac0_nth (a:A list) (i:int) =
    if i < (&0:int) then ARB
    else if num_of_int i < LENGTH a
         then EL (num_of_int i) a
         else ARB`;;

let ntp4vc_sac0_update =
  new_recursive_definition list_RECURSION
   `(!n:num.
     !x:A.
       ntp4vc_sac0_update ([]:A list) n x = []) /\
    (!h:A.
     !t:A list.
     !n:num.
     !x:A.
       ntp4vc_sac0_update (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h (ntp4vc_sac0_update t (PRE n) x))`;;

let ntp4vc_sac0_update_int = new_definition
 `ntp4vc_sac0_update_int (a:A list) (i:int) (x:A) =
    if i < (&0:int) then a
    else ntp4vc_sac0_update a (num_of_int i) x`;;

let ntp4vc_sac0_permutation = new_definition
 `ntp4vc_sac0_permutation (l:int) (p:int list) <=>
    ((&0:int) <= l /\ l <= (&(LENGTH p):int)) /\
    (!i:int.
       (&0:int) <= i /\ i < l
       ==>
       (&0:int) <= ntp4vc_sac0_nth_int p i /\
       ntp4vc_sac0_nth_int p i < l) /\
    (!i j:int.
       (&0:int) <= i /\ i < l
       ==>
       (&0:int) <= j /\ j < l
       ==>
       ~(i = j)
       ==>
       ~(ntp4vc_sac0_nth_int p i =
         ntp4vc_sac0_nth_int p j))`;;

let ntp4vc_sac0_permutation_pair = new_definition
 `ntp4vc_sac0_permutation_pair
    (l:int) (p:int list) (invp:int list) <=>
    ntp4vc_sac0_permutation l p /\
    ntp4vc_sac0_permutation l invp /\
    (!i:int.
       (&0:int) <= i /\ i < l
       ==>
       ntp4vc_sac0_nth_int
         p (ntp4vc_sac0_nth_int invp i) = i) /\
    (!i:int.
       (&0:int) <= i /\ i < l
       ==>
       ntp4vc_sac0_nth_int
         invp (ntp4vc_sac0_nth_int p i) = i)`;;

let ntp4vc_sac0_valid_chunk = new_definition
 `ntp4vc_sac0_valid_chunk (a:A list) (ofs:int) (len:int) <=>
    (&0:int) <= ofs /\
    ofs <= ofs + len /\
    ofs + len <= (&(LENGTH a):int)`;;

let ntp4vc_sac0_copy = new_definition
 `ntp4vc_sac0_copy
    (src:A list) (dst:A list) (ofs:int) (len:int) <=>
    ntp4vc_sac0_valid_chunk src ofs len /\
    LENGTH src = LENGTH dst /\
    (!i:int.
       ofs <= i /\ i < ofs + len
       ==> ntp4vc_sac0_nth dst i = ntp4vc_sac0_nth src i)`;;

let ntp4vc_sac0_all_shuffled_chunks = new_definition
 `ntp4vc_sac0_all_shuffled_chunks
    (src:A list) (dst:A list) (start:int)
    (sigma:int list) (k:int) (upper:int) <=>
    !j':int.
      (&0:int) <= j' /\ j' < upper
      ==>
      ntp4vc_sac0_copy
        src dst
        (start + ntp4vc_sac0_nth_int sigma j' * k) k`;;

let ntp4vc_sac0_update_function_equal = new_definition
 `ntp4vc_sac0_update_function_equal
    (a:A list) (i:int) (x:A) <=>
    (\r:int.
       ntp4vc_sac0_nth
         (ntp4vc_sac0_update_int a i x) r) =
    (\r:int.
       if r = i then x else ntp4vc_sac0_nth a r)`;;

let ntp4vc_sac0_i_step_conclusion = new_definition
 `ntp4vc_sac0_i_step_conclusion
    (src:A list) (dst3:A list) (start:int) (startj:int)
    (sigma:int list) (k:int) (s:int) (m:int) (j:int) (i:int) <=>
    let o4 = startj + i in
    ((&0:int) <= o4 /\ o4 < (&(LENGTH src):int)) /\
    (let o5 = ntp4vc_sac0_nth src o4 in
     let o6 = startj + i in
     ((&0:int) <= o6 /\ o6 < (&(LENGTH dst3):int)) /\
     (LENGTH
        (ntp4vc_sac0_update_int dst3 o6 o5) =
      LENGTH dst3
      ==>
      ntp4vc_sac0_update_function_equal dst3 o6 o5
      ==>
      ntp4vc_sac0_copy
        src
        (ntp4vc_sac0_update_int dst3 o6 o5)
        (&0:int) (s * m) /\
      ntp4vc_sac0_all_shuffled_chunks
        src
        (ntp4vc_sac0_update_int dst3 o6 o5)
        start sigma k j /\
      ntp4vc_sac0_copy
        src
        (ntp4vc_sac0_update_int dst3 o6 o5)
        startj (i + (&1:int))))`;;

let ntp4vc_sac0_all_i_steps = new_definition
 `ntp4vc_sac0_all_i_steps
    (src:A list) (dst3:A list) (start:int) (startj:int)
    (sigma:int list) (k:int) (s:int) (m:int) (j:int) (o3:int) <=>
    !i:int.
      ((&0:int) <= i /\ i <= o3) /\
      ntp4vc_sac0_copy src dst3 (&0:int) (s * m) /\
      ntp4vc_sac0_all_shuffled_chunks
        src dst3 start sigma k j /\
      ntp4vc_sac0_copy src dst3 startj i
      ==>
      ntp4vc_sac0_i_step_conclusion
        src dst3 start startj sigma k s m j i`;;

let ntp4vc_sac0_dst3_body = new_definition
 `ntp4vc_sac0_dst3_body
    (src:A list) (dst3:A list) (start:int) (startj:int)
    (sigma:int list) (k:int) (s:int) (m:int) (j:int) (o3:int) <=>
    ntp4vc_sac0_all_i_steps
      src dst3 start startj sigma k s m j o3 /\
    (ntp4vc_sac0_copy src dst3 (&0:int) (s * m) /\
     ntp4vc_sac0_all_shuffled_chunks
       src dst3 start sigma k j /\
     ntp4vc_sac0_copy src dst3 startj (o3 + (&1:int))
     ==>
     ntp4vc_sac0_copy src dst3 (&0:int) (s * m) /\
     ntp4vc_sac0_all_shuffled_chunks
       src dst3 start sigma k (j + (&1:int)))`;;

let ntp4vc_sac0_all_dst3_loops = new_definition
 `ntp4vc_sac0_all_dst3_loops
    (src:A list) (dst2:A list) (start:int) (startj:int)
    (sigma:int list) (k:int) (s:int) (m:int) (j:int) (o3:int) <=>
    !dst3:A list.
      LENGTH dst3 = LENGTH dst2
      ==>
      ntp4vc_sac0_dst3_body
        src dst3 start startj sigma k s m j o3`;;

let ntp4vc_sac0_j_step_conclusion = new_definition
 `ntp4vc_sac0_j_step_conclusion
    (src:A list) (dst2:A list) (start:int)
    (sigma:int list) (k:int) (s:int) (m:int) (j:int) <=>
    ((&0:int) <= j /\ j < (&(LENGTH sigma):int)) /\
    (let startj =
       start + ntp4vc_sac0_nth_int sigma j * k in
     let o3 = k - (&1:int) in
     ((&0:int) <= o3 + (&1:int)
      ==>
      (ntp4vc_sac0_copy src dst2 (&0:int) (s * m) /\
       ntp4vc_sac0_all_shuffled_chunks
         src dst2 start sigma k j /\
       ntp4vc_sac0_copy src dst2 startj (&0:int)) /\
      ntp4vc_sac0_all_dst3_loops
        src dst2 start startj sigma k s m j o3) /\
     (o3 + (&1:int) < (&0:int)
      ==>
      ntp4vc_sac0_copy src dst2 (&0:int) (s * m) /\
      ntp4vc_sac0_all_shuffled_chunks
        src dst2 start sigma k (j + (&1:int))))`;;

let ntp4vc_sac0_all_j_steps = new_definition
 `ntp4vc_sac0_all_j_steps
    (src:A list) (dst2:A list) (start:int)
    (sigma:int list) (k:int) (s:int) (m:int) (o2:int) <=>
    !j:int.
      ((&0:int) <= j /\ j <= o2) /\
      ntp4vc_sac0_copy src dst2 (&0:int) (s * m) /\
      ntp4vc_sac0_all_shuffled_chunks
        src dst2 start sigma k j
      ==>
      ntp4vc_sac0_j_step_conclusion
        src dst2 start sigma k s m j`;;

let ntp4vc_sac0_dst2_body = new_definition
 `ntp4vc_sac0_dst2_body
    (src:A list) (dst2:A list) (start:int)
    (sigma:int list) (k:int) (s:int) (m:int) (o2:int) <=>
    ntp4vc_sac0_all_j_steps
      src dst2 start sigma k s m o2 /\
    (ntp4vc_sac0_copy src dst2 (&0:int) (s * m) /\
     ntp4vc_sac0_all_shuffled_chunks
       src dst2 start sigma k (o2 + (&1:int))
     ==>
     ntp4vc_sac0_copy
       src dst2 (&0:int) ((s + (&1:int)) * m))`;;

let ntp4vc_sac0_all_dst2_loops = new_definition
 `ntp4vc_sac0_all_dst2_loops
    (src:A list) (dst1:A list) (start:int)
    (sigma:int list) (k:int) (s:int) (m:int) (o2:int) <=>
    !dst2:A list.
      LENGTH dst2 = LENGTH dst1
      ==>
      ntp4vc_sac0_dst2_body
        src dst2 start sigma k s m o2`;;

let ntp4vc_sac0_sigma_body = new_definition
 `ntp4vc_sac0_sigma_body
    (src:A list) (dst1:A list) (start:int)
    (sigma:int list) (k:int) (l:int) (s:int) (m:int) <=>
    let o2 = l - (&1:int) in
    ((&0:int) <= o2 + (&1:int)
     ==>
     (ntp4vc_sac0_copy src dst1 (&0:int) (s * m) /\
      ntp4vc_sac0_all_shuffled_chunks
        src dst1 start sigma k (&0:int)) /\
     ntp4vc_sac0_all_dst2_loops
       src dst1 start sigma k s m o2) /\
    (o2 + (&1:int) < (&0:int)
     ==>
     ntp4vc_sac0_copy
       src dst1 (&0:int) ((s + (&1:int)) * m))`;;

let ntp4vc_sac0_all_permutations = new_definition
 `ntp4vc_sac0_all_permutations
    (src:A list) (dst1:A list) (start:int)
    (k:int) (l:int) (s:int) (m:int) <=>
    !sigma invsigma:int list.
      (LENGTH sigma = LENGTH invsigma /\
       (&(LENGTH invsigma):int) = l) /\
      ntp4vc_sac0_permutation_pair l sigma invsigma
      ==>
      ntp4vc_sac0_sigma_body
        src dst1 start sigma k l s m`;;

let ntp4vc_sac0_s_body = new_definition
 `ntp4vc_sac0_s_body
    (src:A list) (dst1:A list)
    (k:int) (l:int) (s:int) (m:int) <=>
    let start = s * m in
    (&0:int) < l /\
    ntp4vc_sac0_all_permutations
      src dst1 start k l s m`;;

let ntp4vc_sac0_all_s_loops = new_definition
 `ntp4vc_sac0_all_s_loops
    (src:A list) (dst1:A list)
    (k:int) (l:int) (m:int) (o1:int) <=>
    !s:int.
      ((&0:int) <= s /\ s <= o1) /\
      ntp4vc_sac0_copy src dst1 (&0:int) (s * m)
      ==>
      ntp4vc_sac0_s_body src dst1 k l s m`;;

let ntp4vc_sac0_remainder_i_step_conclusion = new_definition
 `ntp4vc_sac0_remainder_i_step_conclusion
    (src:A list) (dst2:A list)
    (last:int) (q:int) (m:int) (i:int) <=>
    let o3 = last + i in
    ((&0:int) <= o3 /\ o3 < (&(LENGTH src):int)) /\
    (let o4 = ntp4vc_sac0_nth src o3 in
     let o5 = last + i in
     ((&0:int) <= o5 /\ o5 < (&(LENGTH dst2):int)) /\
     (LENGTH
        (ntp4vc_sac0_update_int dst2 o5 o4) =
      LENGTH dst2
      ==>
      ntp4vc_sac0_update_function_equal dst2 o5 o4
      ==>
      ntp4vc_sac0_copy
        src
        (ntp4vc_sac0_update_int dst2 o5 o4)
        (&0:int) (q * m) /\
      ntp4vc_sac0_copy
        src
        (ntp4vc_sac0_update_int dst2 o5 o4)
        last (i + (&1:int))))`;;

let ntp4vc_sac0_all_remainder_i_steps = new_definition
 `ntp4vc_sac0_all_remainder_i_steps
    (src:A list) (dst2:A list)
    (last:int) (q:int) (m:int) (o2:int) <=>
    !i:int.
      ((&0:int) <= i /\ i <= o2) /\
      ntp4vc_sac0_copy src dst2 (&0:int) (q * m) /\
      ntp4vc_sac0_copy src dst2 last i
      ==>
      ntp4vc_sac0_remainder_i_step_conclusion
        src dst2 last q m i`;;

let ntp4vc_sac0_remainder_dst2_body = new_definition
 `ntp4vc_sac0_remainder_dst2_body
    (src:A list) (dst2:A list)
    (last:int) (q:int) (m:int) (o2:int) (full_length:int) <=>
    ntp4vc_sac0_all_remainder_i_steps
      src dst2 last q m o2 /\
    (ntp4vc_sac0_copy src dst2 (&0:int) (q * m) /\
     ntp4vc_sac0_copy src dst2 last (o2 + (&1:int))
     ==>
     ntp4vc_sac0_copy src dst2 (&0:int) full_length)`;;

let ntp4vc_sac0_all_remainder_dst2_loops = new_definition
 `ntp4vc_sac0_all_remainder_dst2_loops
    (src:A list) (before:A list)
    (last:int) (q:int) (m:int) (o2:int) (full_length:int) <=>
    !dst2:A list.
      LENGTH dst2 = LENGTH before
      ==>
      ntp4vc_sac0_remainder_dst2_body
        src dst2 last q m o2 full_length`;;

let ntp4vc_sac0_remainder_body = new_definition
 `ntp4vc_sac0_remainder_body
    (src:A list) (before:A list)
    (q:int) (m:int) (r:int) (full_length:int) <=>
    let last = q * m in
    let o2 = r - (&1:int) in
    ((&0:int) <= o2 + (&1:int)
     ==>
     (ntp4vc_sac0_copy src before (&0:int) (q * m) /\
      ntp4vc_sac0_copy src before last (&0:int)) /\
     ntp4vc_sac0_all_remainder_dst2_loops
       src before last q m o2 full_length) /\
    (o2 + (&1:int) < (&0:int)
     ==>
     ntp4vc_sac0_copy src before (&0:int) full_length)`;;

let ntp4vc_sac0_dst1_body = new_definition
 `ntp4vc_sac0_dst1_body
    (src:A list) (dst1:A list)
    (k:int) (l:int) (q:int) (r:int)
    (m:int) (o1:int) (full_length:int) <=>
    ntp4vc_sac0_all_s_loops src dst1 k l m o1 /\
    (ntp4vc_sac0_copy
       src dst1 (&0:int) ((o1 + (&1:int)) * m)
     ==>
     ntp4vc_sac0_remainder_body
       src dst1 q m r full_length)`;;

let ntp4vc_sac0_all_dst1_loops = new_definition
 `ntp4vc_sac0_all_dst1_loops
    (src:A list) (dst:A list)
    (k:int) (l:int) (q:int) (r:int)
    (m:int) (o1:int) (full_length:int) <=>
    !dst1:A list.
      LENGTH dst1 = LENGTH dst
      ==>
      ntp4vc_sac0_dst1_body
        src dst1 k l q r m o1 full_length`;;

let ntp4vc_sac0_main_conclusion = new_definition
 `ntp4vc_sac0_main_conclusion
    (src:A list) (dst:A list)
    (k:int) (l:int) (q:int) (r:int) <=>
    let m = k * l in
    let o1 = q - (&1:int) in
    ((&0:int) <= o1 + (&1:int)
     ==>
     ntp4vc_sac0_copy src dst (&0:int) ((&0:int) * m) /\
     ntp4vc_sac0_all_dst1_loops
       src dst k l q r m o1 (&(LENGTH dst):int)) /\
    (o1 + (&1:int) < (&0:int)
     ==>
     ntp4vc_sac0_remainder_body
       src dst q m r (&(LENGTH dst):int))`;;

let statement =
 `!src:A list.
  !dst:A list.
  !k l q r:int.
    LENGTH src = LENGTH dst
    ==>
    (&0:int) < (&(LENGTH dst):int)
    ==>
    (&0:int) < k
    ==>
    (&0:int) < l
    ==>
    (&0:int) <= q
    ==>
    (&0:int) <= r
    ==>
    r < k * l
    ==>
    (&(LENGTH dst):int) = q * k * l + r
    ==>
    ntp4vc_sac0_main_conclusion src dst k l q r`;;
