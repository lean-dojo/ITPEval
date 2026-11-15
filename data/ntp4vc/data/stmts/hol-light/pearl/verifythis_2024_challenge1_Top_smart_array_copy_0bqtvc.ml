(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2024_challenge1_Top_smart_array_copy_0bqtvc: the
  verification condition for smart array copying by shuffled subsegments,
  including permutation-pair, chunk-copy, nested loop-invariant, and frame
  conditions. This file contains no proof.
*)

let ntp4vc_sac0b_index = new_definition
 `ntp4vc_sac0b_index (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let ntp4vc_sac0b_nth_int = new_definition
 `ntp4vc_sac0b_nth_int (a:int list) (i:int) =
    if ntp4vc_sac0b_index i < LENGTH a
    then EL (ntp4vc_sac0b_index i) a
    else (&0:int)`;;

let ntp4vc_sac0b_nth = new_definition
 `ntp4vc_sac0b_nth (a:A list) (i:int) =
    if ntp4vc_sac0b_index i < LENGTH a
    then EL (ntp4vc_sac0b_index i) a
    else ARB`;;

let ntp4vc_sac0b_permutation = new_definition
 `ntp4vc_sac0b_permutation (l:int) (p:int list) <=>
    ((&0:int) <= l /\ l <= (&(LENGTH p):int)) /\
    (!i:int.
       (&0:int) <= i /\ i < l
       ==>
       (&0:int) <= ntp4vc_sac0b_nth_int p i /\
       ntp4vc_sac0b_nth_int p i < l) /\
    (!i j:int.
       (&0:int) <= i /\ i < l
       ==>
       (&0:int) <= j /\ j < l
       ==>
       ~(i = j)
       ==>
       ~(ntp4vc_sac0b_nth_int p i =
         ntp4vc_sac0b_nth_int p j))`;;

let ntp4vc_sac0b_permutation_pair = new_definition
 `ntp4vc_sac0b_permutation_pair
    (l:int) (p:int list) (invp:int list) <=>
    ntp4vc_sac0b_permutation l p /\
    ntp4vc_sac0b_permutation l invp /\
    (!i:int.
       (&0:int) <= i /\ i < l
       ==>
       ntp4vc_sac0b_nth_int
         p (ntp4vc_sac0b_nth_int invp i) = i) /\
    (!i:int.
       (&0:int) <= i /\ i < l
       ==>
       ntp4vc_sac0b_nth_int
         invp (ntp4vc_sac0b_nth_int p i) = i)`;;

let ntp4vc_sac0b_valid_chunk = new_definition
 `ntp4vc_sac0b_valid_chunk (a:A list) (ofs:int) (len:int) <=>
    (&0:int) <= ofs /\
    ofs <= ofs + len /\
    ofs + len <= (&(LENGTH a):int)`;;

let ntp4vc_sac0b_copy = new_definition
 `ntp4vc_sac0b_copy
    (src:A list) (dst:A list) (ofs:int) (len:int) <=>
    ntp4vc_sac0b_valid_chunk src ofs len /\
    LENGTH src = LENGTH dst /\
    (!i:int.
       ofs <= i /\ i < ofs + len
       ==> ntp4vc_sac0b_nth dst i = ntp4vc_sac0b_nth src i)`;;

let ntp4vc_sac0b_copy_to = new_definition
 `ntp4vc_sac0b_copy_to
    (src:A list) (dst:A list)
    (ofss:int) (ofsd:int) (len:int) <=>
    ntp4vc_sac0b_valid_chunk src ofss len /\
    ntp4vc_sac0b_valid_chunk dst ofsd len /\
    LENGTH src = LENGTH dst /\
    (!i:int.
       (&0:int) <= i /\ i < len
       ==>
       ntp4vc_sac0b_nth dst (ofsd + i) =
       ntp4vc_sac0b_nth src (ofss + i)) /\
    (!i:int.
       ofsd <= i /\ i < ofsd + len
       ==>
       ntp4vc_sac0b_nth dst i =
       ntp4vc_sac0b_nth src (i + (ofss - ofsd)))`;;

let ntp4vc_sac0b_frame = new_definition
 `ntp4vc_sac0b_frame
    (before:A list) (after:A list) (ofs:int) (len:int) <=>
    (!i:int.
       (&0:int) <= i /\ i < ofs
       ==> ntp4vc_sac0b_nth after i = ntp4vc_sac0b_nth before i) /\
    (!i:int.
       ofs + len <= i /\ i < (&(LENGTH after):int)
       ==> ntp4vc_sac0b_nth after i = ntp4vc_sac0b_nth before i)`;;

let ntp4vc_sac0b_all_shuffled_chunks = new_definition
 `ntp4vc_sac0b_all_shuffled_chunks
    (src:A list) (dst:A list) (start:int)
    (sigma:int list) (k:int) (upper:int) <=>
    !j':int.
      (&0:int) <= j' /\ j' < upper
      ==>
      ntp4vc_sac0b_copy
        src dst
        (start + ntp4vc_sac0b_nth_int sigma j' * k) k`;;

let ntp4vc_sac0b_all_dst3_steps = new_definition
 `ntp4vc_sac0b_all_dst3_steps
    (src:A list) (dst2:A list) (start:int) (startj:int)
    (sigma:int list) (k:int) (s:int) (m:int) (j:int) <=>
    !dst3:A list.
      LENGTH dst3 = LENGTH dst2
      ==>
      ntp4vc_sac0b_copy_to src dst3 startj startj k /\
      ntp4vc_sac0b_frame dst2 dst3 startj k
      ==>
      ntp4vc_sac0b_copy src dst3 (&0:int) (s * m) /\
      ntp4vc_sac0b_all_shuffled_chunks
        src dst3 start sigma k (j + (&1:int))`;;

let ntp4vc_sac0b_j_step_conclusion = new_definition
 `ntp4vc_sac0b_j_step_conclusion
    (src:A list) (dst2:A list) (start:int)
    (sigma:int list) (k:int) (s:int) (m:int) (j:int) <=>
    ((&0:int) <= j /\ j < (&(LENGTH sigma):int)) /\
    (let startj = start + ntp4vc_sac0b_nth_int sigma j * k in
     (LENGTH src = LENGTH dst2 /\
      ntp4vc_sac0b_valid_chunk src startj k /\
      ntp4vc_sac0b_valid_chunk dst2 startj k) /\
     ntp4vc_sac0b_all_dst3_steps
       src dst2 start startj sigma k s m j)`;;

let ntp4vc_sac0b_all_j_steps = new_definition
 `ntp4vc_sac0b_all_j_steps
    (src:A list) (dst2:A list) (start:int)
    (sigma:int list) (k:int) (s:int) (m:int) (o2:int) <=>
    !j:int.
      ((&0:int) <= j /\ j <= o2) /\
      ntp4vc_sac0b_copy src dst2 (&0:int) (s * m) /\
      ntp4vc_sac0b_all_shuffled_chunks
        src dst2 start sigma k j
      ==>
      ntp4vc_sac0b_j_step_conclusion
        src dst2 start sigma k s m j`;;

let ntp4vc_sac0b_dst2_body = new_definition
 `ntp4vc_sac0b_dst2_body
    (src:A list) (dst2:A list) (start:int)
    (sigma:int list) (k:int) (s:int) (m:int) (o2:int) <=>
    ntp4vc_sac0b_all_j_steps
      src dst2 start sigma k s m o2 /\
    (ntp4vc_sac0b_copy src dst2 (&0:int) (s * m) /\
     ntp4vc_sac0b_all_shuffled_chunks
       src dst2 start sigma k (o2 + (&1:int))
     ==>
     ntp4vc_sac0b_copy
       src dst2 (&0:int) ((s + (&1:int)) * m))`;;

let ntp4vc_sac0b_all_dst2_loops = new_definition
 `ntp4vc_sac0b_all_dst2_loops
    (src:A list) (dst1:A list) (start:int)
    (sigma:int list) (k:int) (s:int) (m:int) (o2:int) <=>
    !dst2:A list.
      LENGTH dst2 = LENGTH dst1
      ==>
      ntp4vc_sac0b_dst2_body
        src dst2 start sigma k s m o2`;;

let ntp4vc_sac0b_sigma_body = new_definition
 `ntp4vc_sac0b_sigma_body
    (src:A list) (dst1:A list) (start:int)
    (sigma:int list) (k:int) (l:int) (s:int) (m:int) <=>
    let o2 = l - (&1:int) in
    ((&0:int) <= o2 + (&1:int)
     ==>
     (ntp4vc_sac0b_copy src dst1 (&0:int) (s * m) /\
      ntp4vc_sac0b_all_shuffled_chunks
        src dst1 start sigma k (&0:int)) /\
     ntp4vc_sac0b_all_dst2_loops
       src dst1 start sigma k s m o2) /\
    (o2 + (&1:int) < (&0:int)
     ==>
     ntp4vc_sac0b_copy
       src dst1 (&0:int) ((s + (&1:int)) * m))`;;

let ntp4vc_sac0b_all_permutations = new_definition
 `ntp4vc_sac0b_all_permutations
    (src:A list) (dst1:A list) (start:int)
    (k:int) (l:int) (s:int) (m:int) <=>
    !sigma invsigma:int list.
      (LENGTH sigma = LENGTH invsigma /\
       (&(LENGTH invsigma):int) = l) /\
      ntp4vc_sac0b_permutation_pair l sigma invsigma
      ==>
      ntp4vc_sac0b_sigma_body
        src dst1 start sigma k l s m`;;

let ntp4vc_sac0b_s_body = new_definition
 `ntp4vc_sac0b_s_body
    (src:A list) (dst1:A list)
    (k:int) (l:int) (s:int) (m:int) <=>
    let start = s * m in
    (&0:int) < l /\
    ntp4vc_sac0b_all_permutations
      src dst1 start k l s m`;;

let ntp4vc_sac0b_all_s_loops = new_definition
 `ntp4vc_sac0b_all_s_loops
    (src:A list) (dst1:A list)
    (k:int) (l:int) (m:int) (o1:int) <=>
    !s:int.
      ((&0:int) <= s /\ s <= o1) /\
      ntp4vc_sac0b_copy src dst1 (&0:int) (s * m)
      ==>
      ntp4vc_sac0b_s_body src dst1 k l s m`;;

let ntp4vc_sac0b_all_remainder_results = new_definition
 `ntp4vc_sac0b_all_remainder_results
    (src:A list) (before:A list)
    (last:int) (r:int) (full_length:int) <=>
    !after:A list.
      LENGTH after = LENGTH before
      ==>
      ntp4vc_sac0b_copy_to src after last last r /\
      ntp4vc_sac0b_frame before after last r
      ==>
      ntp4vc_sac0b_copy src after (&0:int) full_length`;;

let ntp4vc_sac0b_remainder_body = new_definition
 `ntp4vc_sac0b_remainder_body
    (src:A list) (before:A list)
    (q:int) (m:int) (r:int) (full_length:int) <=>
    let last = q * m in
    (LENGTH src = LENGTH before /\
     ntp4vc_sac0b_valid_chunk src last r /\
     ntp4vc_sac0b_valid_chunk before last r) /\
    ntp4vc_sac0b_all_remainder_results
      src before last r full_length`;;

let ntp4vc_sac0b_dst1_body = new_definition
 `ntp4vc_sac0b_dst1_body
    (src:A list) (dst1:A list)
    (k:int) (l:int) (q:int) (r:int)
    (m:int) (o1:int) (full_length:int) <=>
    ntp4vc_sac0b_all_s_loops src dst1 k l m o1 /\
    (ntp4vc_sac0b_copy
       src dst1 (&0:int) ((o1 + (&1:int)) * m)
     ==>
     ntp4vc_sac0b_remainder_body
       src dst1 q m r full_length)`;;

let ntp4vc_sac0b_all_dst1_loops = new_definition
 `ntp4vc_sac0b_all_dst1_loops
    (src:A list) (dst:A list)
    (k:int) (l:int) (q:int) (r:int)
    (m:int) (o1:int) (full_length:int) <=>
    !dst1:A list.
      LENGTH dst1 = LENGTH dst
      ==>
      ntp4vc_sac0b_dst1_body
        src dst1 k l q r m o1 full_length`;;

let ntp4vc_sac0b_main_conclusion = new_definition
 `ntp4vc_sac0b_main_conclusion
    (src:A list) (dst:A list)
    (k:int) (l:int) (q:int) (r:int) <=>
    let m = k * l in
    let o1 = q - (&1:int) in
    ((&0:int) <= o1 + (&1:int)
     ==>
     ntp4vc_sac0b_copy src dst (&0:int) ((&0:int) * m) /\
     ntp4vc_sac0b_all_dst1_loops
       src dst k l q r m o1 (&(LENGTH dst):int)) /\
    (o1 + (&1:int) < (&0:int)
     ==>
     ntp4vc_sac0b_remainder_body
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
    ntp4vc_sac0b_main_conclusion src dst k l q r`;;
