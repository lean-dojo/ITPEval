(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2024_challenge1_Top_smart_array_copy_1qtvc: the
  verification condition for smart array copying by independently shuffled
  source and destination subsegments, including permutation pairs, framing,
  list updates, and nested loop-continuation obligations. This file contains
  no proof.
*)

let ntp4vc_sac1_nth_int = new_definition
 `ntp4vc_sac1_nth_int (a:int list) (i:int) =
    if i < (&0:int) then (&0:int)
    else if num_of_int i < LENGTH a
         then EL (num_of_int i) a
         else (&0:int)`;;

let ntp4vc_sac1_nth = new_definition
 `ntp4vc_sac1_nth (a:A list) (i:int) =
    if i < (&0:int) then ARB
    else if num_of_int i < LENGTH a
         then EL (num_of_int i) a
         else ARB`;;

let ntp4vc_sac1_update =
  new_recursive_definition list_RECURSION
   `(!n:num.
     !x:A.
       ntp4vc_sac1_update ([]:A list) n x = []) /\
    (!h:A.
     !t:A list.
     !n:num.
     !x:A.
       ntp4vc_sac1_update (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h (ntp4vc_sac1_update t (PRE n) x))`;;

let ntp4vc_sac1_update_int = new_definition
 `ntp4vc_sac1_update_int (a:A list) (i:int) (x:A) =
    if i < (&0:int) then a
    else ntp4vc_sac1_update a (num_of_int i) x`;;

let ntp4vc_sac1_identity_num =
  new_recursive_definition num_RECURSION
   `(ntp4vc_sac1_identity_num 0 = []) /\
    (!n:num.
       ntp4vc_sac1_identity_num (SUC n) =
       APPEND (ntp4vc_sac1_identity_num n) [(&n:int)])`;;

let ntp4vc_sac1_identity = new_definition
 `ntp4vc_sac1_identity (l:int) =
    if l < (&0:int) then []
    else ntp4vc_sac1_identity_num (num_of_int l)`;;

let ntp4vc_sac1_identity_values = new_definition
 `ntp4vc_sac1_identity_values (a:int list) (l:int) <=>
    !i:int.
      (&0:int) <= i /\ i < l
      ==> ntp4vc_sac1_nth_int a i = i`;;

let ntp4vc_sac1_permutation = new_definition
 `ntp4vc_sac1_permutation (l:int) (p:int list) <=>
    ((&0:int) <= l /\ l <= (&(LENGTH p):int)) /\
    (!i:int.
       (&0:int) <= i /\ i < l
       ==>
       (&0:int) <= ntp4vc_sac1_nth_int p i /\
       ntp4vc_sac1_nth_int p i < l) /\
    (!i j:int.
       (&0:int) <= i /\ i < l
       ==>
       (&0:int) <= j /\ j < l
       ==>
       ~(i = j)
       ==>
       ~(ntp4vc_sac1_nth_int p i =
         ntp4vc_sac1_nth_int p j))`;;

let ntp4vc_sac1_permutation_pair = new_definition
 `ntp4vc_sac1_permutation_pair
    (l:int) (p:int list) (invp:int list) <=>
    ntp4vc_sac1_permutation l p /\
    ntp4vc_sac1_permutation l invp /\
    (!i:int.
       (&0:int) <= i /\ i < l
       ==>
       ntp4vc_sac1_nth_int
         p (ntp4vc_sac1_nth_int invp i) = i) /\
    (!i:int.
       (&0:int) <= i /\ i < l
       ==>
       ntp4vc_sac1_nth_int
         invp (ntp4vc_sac1_nth_int p i) = i)`;;

let ntp4vc_sac1_valid_chunk = new_definition
 `ntp4vc_sac1_valid_chunk (a:A list) (ofs:int) (len:int) <=>
    (&0:int) <= ofs /\
    ofs <= ofs + len /\
    ofs + len <= (&(LENGTH a):int)`;;

let ntp4vc_sac1_copy_to = new_definition
 `ntp4vc_sac1_copy_to
    (src:A list) (dst:A list)
    (ofss:int) (ofsd:int) (len:int) <=>
    ntp4vc_sac1_valid_chunk src ofss len /\
    ntp4vc_sac1_valid_chunk dst ofsd len /\
    LENGTH src = LENGTH dst /\
    (!i:int.
       (&0:int) <= i /\ i < len
       ==>
       ntp4vc_sac1_nth dst (ofsd + i) =
       ntp4vc_sac1_nth src (ofss + i)) /\
    (!i:int.
       ofsd <= i /\ i < ofsd + len
       ==>
       ntp4vc_sac1_nth dst i =
       ntp4vc_sac1_nth src (i + (ofss - ofsd)))`;;

let ntp4vc_sac1_copy_perm = new_definition
 `ntp4vc_sac1_copy_perm
    (src:A list) (dst:A list) (size:int)
    (p:int list) (invp:int list) <=>
    ntp4vc_sac1_valid_chunk src (&0:int) size /\
    LENGTH src = LENGTH dst /\
    ntp4vc_sac1_permutation_pair size p invp /\
    (!i:int.
       (&0:int) <= i /\ i < size
       ==>
       (&0:int) <= ntp4vc_sac1_nth_int p i /\
       ntp4vc_sac1_nth_int p i < size) /\
    (!i:int.
       (&0:int) <= i /\ i < size
       ==>
       (&0:int) <= ntp4vc_sac1_nth_int invp i /\
       ntp4vc_sac1_nth_int invp i < size) /\
    (!i:int.
       (&0:int) <= i /\ i < size
       ==>
       ntp4vc_sac1_nth dst i =
       ntp4vc_sac1_nth
         src (ntp4vc_sac1_nth_int p i)) /\
    (!i:int.
       (&0:int) <= i /\ i < size
       ==>
       ntp4vc_sac1_nth src i =
       ntp4vc_sac1_nth
         dst (ntp4vc_sac1_nth_int invp i))`;;

let ntp4vc_sac1_copy_subsegment = new_definition
 `ntp4vc_sac1_copy_subsegment
    (src:A list) (dst:A list)
    (s:int) (k:int) (l:int) (j:int)
    (sigma:int list) (tau:int list)
    (p:int list) (invp:int list) <=>
    let start = s * (k * l) in
    let starts =
      start + ntp4vc_sac1_nth_int sigma j * k in
    let startd =
      start +
      ntp4vc_sac1_nth_int
        tau (ntp4vc_sac1_nth_int sigma j) * k in
    ntp4vc_sac1_copy_to src dst starts startd k /\
    (!i:int.
       (&0:int) <= i /\ i < k
       ==>
       ntp4vc_sac1_nth_int p (startd + i) =
       starts + i) /\
    (!i:int.
       (&0:int) <= i /\ i < k
       ==>
       ntp4vc_sac1_nth_int invp (starts + i) =
       startd + i)`;;

let ntp4vc_sac1_frame = new_definition
 `ntp4vc_sac1_frame
    (a1:A list) (a2:A list) (ofs:int) (len:int) <=>
    LENGTH a2 = LENGTH a1 /\
    (!i:int.
       (&0:int) <= i /\ i < ofs
       ==> ntp4vc_sac1_nth a2 i = ntp4vc_sac1_nth a1 i) /\
    (!i:int.
       ofs + len <= i /\ i < (&(LENGTH a2):int)
       ==> ntp4vc_sac1_nth a2 i = ntp4vc_sac1_nth a1 i)`;;

let ntp4vc_sac1_all_subsegments_before = new_definition
 `ntp4vc_sac1_all_subsegments_before
    (src:A list) (dst:A list)
    (s:int) (k:int) (l:int) (upper:int)
    (sigma:int list) (tau:int list)
    (p:int list) (invp:int list) <=>
    !j':int.
      (&0:int) <= j' /\ j' < upper
      ==>
      ntp4vc_sac1_copy_subsegment
        src dst s k l j' sigma tau p invp`;;

let ntp4vc_sac1_index_prefix = new_definition
 `ntp4vc_sac1_index_prefix
    (a:int list) (index_base:int)
    (value_base:int) (upper:int) <=>
    !i:int.
      (&0:int) <= i /\ i < upper
      ==>
      ntp4vc_sac1_nth_int a (index_base + i) =
      value_base + i`;;

let ntp4vc_sac1_update_function_equal = new_definition
 `ntp4vc_sac1_update_function_equal
    (a:A list) (i:int) (x:A) <=>
    (\r:int.
       ntp4vc_sac1_nth
         (ntp4vc_sac1_update_int a i x) r) =
    (\r:int.
       if r = i then x else ntp4vc_sac1_nth a r)`;;

let ntp4vc_sac1_inner_update_result = new_definition
 `ntp4vc_sac1_inner_update_result
    (src:A list)
    (dst_before:A list) (dst:A list)
    (p_before:int list) (p:int list)
    (invp_before:int list) (invp:int list)
    (s:int) (k:int) (l:int) (j:int)
    (sigma:int list) (tau:int list)
    (m:int) (startsrc:int) (startdst:int) (i:int) <=>
    let source_index = startsrc + i in
    let value = ntp4vc_sac1_nth src source_index in
    let destination_index = startdst + i in
    let dst_next =
      ntp4vc_sac1_update_int dst destination_index value in
    let p_value = startsrc + i in
    let p_index = startdst + i in
    let p_next =
      ntp4vc_sac1_update_int p p_index p_value in
    let invp_value = startdst + i in
    let invp_index = startsrc + i in
    let invp_next =
      ntp4vc_sac1_update_int invp invp_index invp_value in
    ((&0:int) <= source_index /\
     source_index < (&(LENGTH src):int)) /\
    ((&0:int) <= destination_index /\
     destination_index < (&(LENGTH dst):int)) /\
    (LENGTH dst_next = LENGTH dst
     ==>
     ntp4vc_sac1_update_function_equal
       dst destination_index value
     ==>
     ((&0:int) <= p_index /\
      p_index < (&(LENGTH p):int)) /\
     (LENGTH p_next = LENGTH p
      ==>
      ntp4vc_sac1_update_function_equal p p_index p_value
      ==>
      ((&0:int) <= invp_index /\
       invp_index < (&(LENGTH invp):int)) /\
      (LENGTH invp_next = LENGTH invp
       ==>
       ntp4vc_sac1_update_function_equal
         invp invp_index invp_value
       ==>
       ntp4vc_sac1_frame dst_before dst_next startdst k /\
       ntp4vc_sac1_frame p_before p_next startdst k /\
       ntp4vc_sac1_frame invp_before invp_next startsrc k /\
       ntp4vc_sac1_permutation_pair (s * m) p_next invp_next /\
       ntp4vc_sac1_copy_perm
         src dst_next (s * m) p_next invp_next /\
       ntp4vc_sac1_copy_to
         src dst_next startsrc startdst (i + (&1:int)) /\
       ntp4vc_sac1_index_prefix
         p_next startdst startsrc (i + (&1:int)) /\
       ntp4vc_sac1_index_prefix
         invp_next startsrc startdst (i + (&1:int)) /\
       ntp4vc_sac1_all_subsegments_before
         src dst_next s k l j sigma tau p_next invp_next)))`;;

let ntp4vc_sac1_all_inner_indices = new_definition
 `ntp4vc_sac1_all_inner_indices
    (src:A list)
    (dst_before:A list) (dst:A list)
    (p_before:int list) (p:int list)
    (invp_before:int list) (invp:int list)
    (s:int) (k:int) (l:int) (j:int)
    (sigma:int list) (tau:int list)
    (m:int) (startsrc:int) (startdst:int) (upper:int) <=>
    !i:int.
      ((&0:int) <= i /\ i <= upper) /\
      ntp4vc_sac1_frame dst_before dst startdst k /\
      ntp4vc_sac1_frame p_before p startdst k /\
      ntp4vc_sac1_frame invp_before invp startsrc k /\
      ntp4vc_sac1_permutation_pair (s * m) p invp /\
      ntp4vc_sac1_copy_perm src dst (s * m) p invp /\
      ntp4vc_sac1_copy_to src dst startsrc startdst i /\
      ntp4vc_sac1_index_prefix p startdst startsrc i /\
      ntp4vc_sac1_index_prefix invp startsrc startdst i /\
      ntp4vc_sac1_all_subsegments_before
        src dst s k l j sigma tau p invp
      ==>
      ntp4vc_sac1_inner_update_result
        src dst_before dst p_before p invp_before invp
        s k l j sigma tau m startsrc startdst i`;;

let ntp4vc_sac1_inner_state_body = new_definition
 `ntp4vc_sac1_inner_state_body
    (src:A list)
    (dst_before:A list) (dst:A list)
    (p_before:int list) (p:int list)
    (invp_before:int list) (invp:int list)
    (s:int) (k:int) (l:int) (j:int)
    (sigma:int list) (tau:int list)
    (m:int) (startsrc:int) (startdst:int) (upper:int) <=>
    ntp4vc_sac1_all_inner_indices
      src dst_before dst p_before p invp_before invp
      s k l j sigma tau m startsrc startdst upper /\
    (ntp4vc_sac1_frame dst_before dst startdst k /\
     ntp4vc_sac1_frame p_before p startdst k /\
     ntp4vc_sac1_frame invp_before invp startsrc k /\
     ntp4vc_sac1_permutation_pair (s * m) p invp /\
     ntp4vc_sac1_copy_perm src dst (s * m) p invp /\
     ntp4vc_sac1_copy_to
       src dst startsrc startdst (upper + (&1:int)) /\
     ntp4vc_sac1_index_prefix
       p startdst startsrc (upper + (&1:int)) /\
     ntp4vc_sac1_index_prefix
       invp startsrc startdst (upper + (&1:int)) /\
     ntp4vc_sac1_all_subsegments_before
       src dst s k l j sigma tau p invp
     ==>
     ntp4vc_sac1_permutation_pair (s * m) p invp /\
     ntp4vc_sac1_copy_perm src dst (s * m) p invp /\
     ntp4vc_sac1_all_subsegments_before
       src dst s k l (j + (&1:int)) sigma tau p invp)`;;

let ntp4vc_sac1_all_inner_states = new_definition
 `ntp4vc_sac1_all_inner_states
    (src:A list)
    (dst_before:A list)
    (p_before:int list)
    (invp_before:int list)
    (s:int) (k:int) (l:int) (j:int)
    (sigma:int list) (tau:int list)
    (m:int) (startsrc:int) (startdst:int) (upper:int) <=>
    !invp p dst.
      LENGTH invp = LENGTH invp_before
      ==>
      LENGTH p = LENGTH p_before
      ==>
      LENGTH dst = LENGTH dst_before
      ==>
      ntp4vc_sac1_inner_state_body
        src dst_before dst p_before p invp_before invp
        s k l j sigma tau m startsrc startdst upper`;;

let ntp4vc_sac1_inner_loop_vc = new_definition
 `ntp4vc_sac1_inner_loop_vc
    (src:A list) (dst:A list)
    (p:int list) (invp:int list)
    (s:int) (k:int) (l:int) (j:int)
    (sigma:int list) (tau:int list)
    (m:int) (startsrc:int) (startdst:int) <=>
    let upper = k - (&1:int) in
    ((&0:int) <= upper + (&1:int)
     ==>
     (ntp4vc_sac1_frame dst dst startdst k /\
      ntp4vc_sac1_frame p p startdst k /\
      ntp4vc_sac1_frame invp invp startsrc k /\
      ntp4vc_sac1_permutation_pair (s * m) p invp /\
      ntp4vc_sac1_copy_perm src dst (s * m) p invp /\
      ntp4vc_sac1_copy_to
        src dst startsrc startdst (&0:int) /\
      ntp4vc_sac1_index_prefix
        p startdst startsrc (&0:int) /\
      ntp4vc_sac1_index_prefix
        invp startsrc startdst (&0:int) /\
      ntp4vc_sac1_all_subsegments_before
        src dst s k l j sigma tau p invp) /\
     ntp4vc_sac1_all_inner_states
       src dst p invp s k l j sigma tau
       m startsrc startdst upper) /\
    (upper + (&1:int) < (&0:int)
     ==>
     ntp4vc_sac1_permutation_pair (s * m) p invp /\
     ntp4vc_sac1_copy_perm src dst (s * m) p invp /\
     ntp4vc_sac1_all_subsegments_before
       src dst s k l (j + (&1:int)) sigma tau p invp)`;;

let ntp4vc_sac1_subsegment_step_result = new_definition
 `ntp4vc_sac1_subsegment_step_result
    (src:A list) (dst:A list)
    (p:int list) (invp:int list)
    (s:int) (k:int) (l:int) (j:int)
    (sigma:int list) (tau:int list)
    (m:int) (start:int) <=>
    ((&0:int) <= j /\ j < (&(LENGTH sigma):int)) /\
    (let startsrc =
       start + ntp4vc_sac1_nth_int sigma j * k in
     ((&0:int) <= j /\ j < (&(LENGTH sigma):int)) /\
     (let sigma_value = ntp4vc_sac1_nth_int sigma j in
      ((&0:int) <= sigma_value /\
       sigma_value < (&(LENGTH tau):int)) /\
      (let startdst =
         start + ntp4vc_sac1_nth_int tau sigma_value * k in
       ntp4vc_sac1_inner_loop_vc
         src dst p invp s k l j sigma tau
         m startsrc startdst)))`;;

let ntp4vc_sac1_all_subsegment_indices = new_definition
 `ntp4vc_sac1_all_subsegment_indices
    (src:A list) (dst:A list)
    (p:int list) (invp:int list)
    (s:int) (k:int) (l:int)
    (sigma:int list) (tau:int list)
    (m:int) (start:int) (upper:int) <=>
    !j:int.
      ((&0:int) <= j /\ j <= upper) /\
      ntp4vc_sac1_permutation_pair (s * m) p invp /\
      ntp4vc_sac1_copy_perm src dst (s * m) p invp /\
      ntp4vc_sac1_all_subsegments_before
        src dst s k l j sigma tau p invp
      ==>
      ntp4vc_sac1_subsegment_step_result
        src dst p invp s k l j sigma tau m start`;;

let ntp4vc_sac1_subsegment_state_body = new_definition
 `ntp4vc_sac1_subsegment_state_body
    (src:A list) (dst:A list)
    (p:int list) (invp:int list)
    (s:int) (k:int) (l:int)
    (sigma:int list) (tau:int list)
    (m:int) (start:int) (upper:int) <=>
    ntp4vc_sac1_all_subsegment_indices
      src dst p invp s k l sigma tau m start upper /\
    (ntp4vc_sac1_permutation_pair (s * m) p invp /\
     ntp4vc_sac1_copy_perm src dst (s * m) p invp /\
     ntp4vc_sac1_all_subsegments_before
       src dst s k l (upper + (&1:int)) sigma tau p invp
     ==>
     ntp4vc_sac1_permutation_pair
       ((s + (&1:int)) * m) p invp /\
     ntp4vc_sac1_copy_perm
       src dst ((s + (&1:int)) * m) p invp)`;;

let ntp4vc_sac1_all_subsegment_states = new_definition
 `ntp4vc_sac1_all_subsegment_states
    (src:A list) (dst_before:A list)
    (p_before:int list) (invp_before:int list)
    (s:int) (k:int) (l:int)
    (sigma:int list) (tau:int list)
    (m:int) (start:int) (upper:int) <=>
    !invp p dst.
      LENGTH invp = LENGTH invp_before
      ==>
      LENGTH p = LENGTH p_before
      ==>
      LENGTH dst = LENGTH dst_before
      ==>
      ntp4vc_sac1_subsegment_state_body
        src dst p invp s k l sigma tau m start upper`;;

let ntp4vc_sac1_tau_loop_vc = new_definition
 `ntp4vc_sac1_tau_loop_vc
    (src:A list) (dst:A list)
    (p:int list) (invp:int list)
    (s:int) (k:int) (l:int)
    (sigma:int list) (tau:int list) (m:int) <=>
    let upper = l - (&1:int) in
    let start = s * m in
    ((&0:int) <= upper + (&1:int)
     ==>
     (ntp4vc_sac1_permutation_pair (s * m) p invp /\
      ntp4vc_sac1_copy_perm src dst (s * m) p invp /\
      ntp4vc_sac1_all_subsegments_before
        src dst s k l (&0:int) sigma tau p invp) /\
     ntp4vc_sac1_all_subsegment_states
       src dst p invp s k l sigma tau m start upper) /\
    (upper + (&1:int) < (&0:int)
     ==>
     ntp4vc_sac1_permutation_pair
       ((s + (&1:int)) * m) p invp /\
     ntp4vc_sac1_copy_perm
       src dst ((s + (&1:int)) * m) p invp)`;;

let ntp4vc_sac1_all_tau_permutations = new_definition
 `ntp4vc_sac1_all_tau_permutations
    (src:A list) (dst:A list)
    (p:int list) (invp:int list)
    (s:int) (k:int) (l:int)
    (sigma:int list) (m:int) <=>
    !tau invtau:int list.
      (LENGTH tau = LENGTH invtau /\
       (&(LENGTH invtau):int) = l) /\
      ntp4vc_sac1_permutation_pair l tau invtau
      ==>
      ntp4vc_sac1_tau_loop_vc
        src dst p invp s k l sigma tau m`;;

let ntp4vc_sac1_all_sigma_permutations = new_definition
 `ntp4vc_sac1_all_sigma_permutations
    (src:A list) (dst:A list)
    (p:int list) (invp:int list)
    (s:int) (k:int) (l:int) (m:int) <=>
    !sigma invsigma:int list.
      (LENGTH sigma = LENGTH invsigma /\
       (&(LENGTH invsigma):int) = l) /\
      ntp4vc_sac1_permutation_pair l sigma invsigma
      ==>
      (&0:int) < l /\
      ntp4vc_sac1_all_tau_permutations
        src dst p invp s k l sigma m`;;

let ntp4vc_sac1_segment_step_result = new_definition
 `ntp4vc_sac1_segment_step_result
    (src:A list) (dst:A list)
    (p:int list) (invp:int list)
    (s:int) (k:int) (l:int) (m:int) <=>
    (&0:int) < l /\
    ntp4vc_sac1_all_sigma_permutations
      src dst p invp s k l m`;;

let ntp4vc_sac1_all_segment_indices = new_definition
 `ntp4vc_sac1_all_segment_indices
    (src:A list) (dst:A list)
    (p:int list) (invp:int list)
    (k:int) (l:int) (m:int) (upper:int) <=>
    !s:int.
      ((&0:int) <= s /\ s <= upper) /\
      ntp4vc_sac1_permutation_pair (s * m) p invp /\
      ntp4vc_sac1_copy_perm src dst (s * m) p invp
      ==>
      ntp4vc_sac1_segment_step_result
        src dst p invp s k l m`;;

let ntp4vc_sac1_tail_step_result = new_definition
 `ntp4vc_sac1_tail_step_result
    (src:A list) (dst:A list)
    (p:int list) (invp:int list)
    (last:int) (i:int) <=>
    let source_index = last + i in
    let value = ntp4vc_sac1_nth src source_index in
    let destination_index = last + i in
    let dst_next =
      ntp4vc_sac1_update_int dst destination_index value in
    let p_value = last + i in
    let p_index = last + i in
    let p_next =
      ntp4vc_sac1_update_int p p_index p_value in
    let invp_value = last + i in
    let invp_index = last + i in
    let invp_next =
      ntp4vc_sac1_update_int invp invp_index invp_value in
    ((&0:int) <= source_index /\
     source_index < (&(LENGTH src):int)) /\
    ((&0:int) <= destination_index /\
     destination_index < (&(LENGTH dst):int)) /\
    (LENGTH dst_next = LENGTH dst
     ==>
     ntp4vc_sac1_update_function_equal
       dst destination_index value
     ==>
     ((&0:int) <= p_index /\
      p_index < (&(LENGTH p):int)) /\
     (LENGTH p_next = LENGTH p
      ==>
      ntp4vc_sac1_update_function_equal p p_index p_value
      ==>
      ((&0:int) <= invp_index /\
       invp_index < (&(LENGTH invp):int)) /\
      (LENGTH invp_next = LENGTH invp
       ==>
       ntp4vc_sac1_update_function_equal
         invp invp_index invp_value
       ==>
       ntp4vc_sac1_permutation_pair
         (last + (i + (&1:int))) p_next invp_next /\
       ntp4vc_sac1_copy_perm
         src dst_next
         (last + (i + (&1:int))) p_next invp_next)))`;;

let ntp4vc_sac1_all_tail_indices = new_definition
 `ntp4vc_sac1_all_tail_indices
    (src:A list) (dst:A list)
    (p:int list) (invp:int list)
    (last:int) (upper:int) <=>
    !i:int.
      ((&0:int) <= i /\ i <= upper) /\
      ntp4vc_sac1_permutation_pair (last + i) p invp /\
      ntp4vc_sac1_copy_perm src dst (last + i) p invp
      ==>
      ntp4vc_sac1_tail_step_result
        src dst p invp last i`;;

let ntp4vc_sac1_tail_state_body = new_definition
 `ntp4vc_sac1_tail_state_body
    (src:A list) (dst:A list)
    (p:int list) (invp:int list)
    (last:int) (upper:int) (full_length:int) <=>
    ntp4vc_sac1_all_tail_indices
      src dst p invp last upper /\
    (ntp4vc_sac1_permutation_pair
       (last + (upper + (&1:int))) p invp /\
     ntp4vc_sac1_copy_perm
       src dst (last + (upper + (&1:int))) p invp
     ==>
     ntp4vc_sac1_copy_perm
       src dst full_length p invp)`;;

let ntp4vc_sac1_all_tail_states = new_definition
 `ntp4vc_sac1_all_tail_states
    (src:A list) (dst_before:A list)
    (p_before:int list) (invp_before:int list)
    (last:int) (upper:int) (full_length:int) <=>
    !invp p dst.
      LENGTH invp = LENGTH invp_before
      ==>
      LENGTH p = LENGTH p_before
      ==>
      LENGTH dst = LENGTH dst_before
      ==>
      ntp4vc_sac1_tail_state_body
        src dst p invp last upper full_length`;;

let ntp4vc_sac1_tail_vc = new_definition
 `ntp4vc_sac1_tail_vc
    (src:A list) (dst:A list)
    (p:int list) (invp:int list)
    (last:int) (r:int) (full_length:int) <=>
    let upper = r - (&1:int) in
    ((&0:int) <= upper + (&1:int)
     ==>
     (ntp4vc_sac1_permutation_pair
        (last + (&0:int)) p invp /\
      ntp4vc_sac1_copy_perm
        src dst (last + (&0:int)) p invp) /\
     ntp4vc_sac1_all_tail_states
       src dst p invp last upper full_length) /\
    (upper + (&1:int) < (&0:int)
     ==>
     ntp4vc_sac1_copy_perm
       src dst full_length p invp)`;;

let ntp4vc_sac1_outer_state_body = new_definition
 `ntp4vc_sac1_outer_state_body
    (src:A list) (dst:A list)
    (p:int list) (invp:int list)
    (k:int) (l:int) (q:int) (r:int)
    (m:int) (upper:int) (full_length:int) <=>
    ntp4vc_sac1_all_segment_indices
      src dst p invp k l m upper /\
    (ntp4vc_sac1_permutation_pair
       ((upper + (&1:int)) * m) p invp /\
     ntp4vc_sac1_copy_perm
       src dst ((upper + (&1:int)) * m) p invp
     ==>
     ntp4vc_sac1_tail_vc
       src dst p invp (q * m) r full_length)`;;

let ntp4vc_sac1_all_outer_states = new_definition
 `ntp4vc_sac1_all_outer_states
    (src:A list) (dst_before:A list)
    (p_before:int list) (invp_before:int list)
    (k:int) (l:int) (q:int) (r:int)
    (m:int) (upper:int) (full_length:int) <=>
    !invp p dst.
      LENGTH invp = LENGTH invp_before
      ==>
      LENGTH p = LENGTH p_before
      ==>
      LENGTH dst = LENGTH dst_before
      ==>
      ntp4vc_sac1_outer_state_body
        src dst p invp k l q r m upper full_length`;;

let ntp4vc_sac1_outer_loop_vc = new_definition
 `ntp4vc_sac1_outer_loop_vc
    (src:A list) (dst:A list)
    (p:int list) (invp:int list)
    (k:int) (l:int) (q:int) (r:int)
    (full_length:int) <=>
    let m = k * l in
    let upper = q - (&1:int) in
    ((&0:int) <= upper + (&1:int)
     ==>
     (ntp4vc_sac1_permutation_pair
        ((&0:int) * m) p invp /\
      ntp4vc_sac1_copy_perm
        src dst ((&0:int) * m) p invp) /\
     ntp4vc_sac1_all_outer_states
       src dst p invp k l q r m upper full_length) /\
    (upper + (&1:int) < (&0:int)
     ==>
     ntp4vc_sac1_tail_vc
       src dst p invp (q * m) r full_length)`;;

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
    (&0:int) < (&(LENGTH dst):int) /\
    (let full_length = (&(LENGTH dst):int) in
     let p = ntp4vc_sac1_identity full_length in
     (LENGTH p = LENGTH dst /\
      ntp4vc_sac1_identity_values p full_length /\
      ntp4vc_sac1_permutation_pair full_length p p
      ==>
      (&0:int) < (&(LENGTH dst):int) /\
      (let invp = ntp4vc_sac1_identity full_length in
       LENGTH invp = LENGTH dst /\
       ntp4vc_sac1_identity_values invp full_length /\
       ntp4vc_sac1_permutation_pair full_length invp invp
       ==>
       ntp4vc_sac1_outer_loop_vc
         src dst p invp k l q r full_length)))`;;
