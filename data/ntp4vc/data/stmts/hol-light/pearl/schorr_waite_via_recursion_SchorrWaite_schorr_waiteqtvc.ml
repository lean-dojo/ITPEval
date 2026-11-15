(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/schorr_waite_via_recursion_SchorrWaite_schorr_waiteqtvc: the
  recursive Schorr-Waite graph-marking verification condition, including
  body transitions, recursive traversal, loop invariants, pointer
  restoration, coloring, and termination variants. This file contains no proof.
*)

let ntp4vc_swr_color_INDUCT,ntp4vc_swr_color_RECURSION =
  define_type
   "ntp4vc_swr_color =
      NTP4VC_SWR_White
    | NTP4VC_SWR_Black (int option)";;

let ntp4vc_swr_block_size = new_definition
 `ntp4vc_swr_block_size
    (mem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color))) =
    FST mem`;;

let ntp4vc_swr_accessor = new_definition
 `ntp4vc_swr_accessor
    (mem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color))) =
    FST (SND mem)`;;

let ntp4vc_swr_colors = new_definition
 `ntp4vc_swr_colors
    (mem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color))) =
    SND (SND mem)`;;

let ntp4vc_swr_update = new_definition
 `ntp4vc_swr_update (f:A->B) (x:A) (y:B) =
    \z:A. if z = x then y else f z`;;

let ntp4vc_swr_with_accessor = new_definition
 `ntp4vc_swr_with_accessor
    (mem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (acc:A->int->A) =
    (ntp4vc_swr_block_size mem,
     (acc,ntp4vc_swr_colors mem))`;;

let ntp4vc_swr_with_colors = new_definition
 `ntp4vc_swr_with_colors
    (mem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (cl:A->ntp4vc_swr_color) =
    (ntp4vc_swr_block_size mem,
     (ntp4vc_swr_accessor mem,cl))`;;

let ntp4vc_swr_with_accessor_and_colors = new_definition
 `ntp4vc_swr_with_accessor_and_colors
    (mem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (acc:A->int->A)
    (cl:A->ntp4vc_swr_color) =
    (ntp4vc_swr_block_size mem,(acc,cl))`;;

let ntp4vc_swr_black = new_definition
 `ntp4vc_swr_black (c:ntp4vc_swr_color) <=>
    ~(c = NTP4VC_SWR_White)`;;

let ntp4vc_swr_edge = new_definition
 `ntp4vc_swr_edge
    (null:A)
    (mem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (x:A) (y:A) <=>
    ~(x = null) /\
    (?n:int.
       (&0:int) <= n /\
       n < ntp4vc_swr_block_size mem x /\
       ntp4vc_swr_accessor mem x n = y)`;;

let ntp4vc_swr_path_list =
  new_recursive_definition list_RECURSION
   `(!null:A.
     !mem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)).
     !x y:A.
       ntp4vc_swr_path_list null mem x y [] <=> x = y) /\
    (!null:A.
     !mem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)).
     !x y h:A.
     !tail:A list.
       ntp4vc_swr_path_list null mem x y (CONS h tail) <=>
       h = x /\
       (?z:A.
          ntp4vc_swr_edge null mem x z /\
          ntp4vc_swr_path_list null mem z y tail))`;;

let ntp4vc_swr_path = new_definition
 `ntp4vc_swr_path
    (null:A)
    (mem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (x:A) (y:A) <=>
    ?p:A list. ntp4vc_swr_path_list null mem x y p`;;

let ntp4vc_swr_well_colored_on = new_definition
 `ntp4vc_swr_well_colored_on
    (null:A)
    (graph:A->bool)
    (gray:A->bool)
    (base:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (cl:A->ntp4vc_swr_color) <=>
    gray SUBSET graph /\
    (!x y:A.
       x IN graph /\
       ntp4vc_swr_edge null base x y /\
       ~(y = null) /\
       ntp4vc_swr_black (cl x)
       ==> x IN gray \/ ntp4vc_swr_black (cl y)) /\
    (!x:A. x IN gray ==> ntp4vc_swr_black (cl x))`;;

let ntp4vc_swr_unchanged = new_definition
 `ntp4vc_swr_unchanged
    (null:A)
    (mem1:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (mem2:(A->int)#((A->int->A)#(A->ntp4vc_swr_color))) <=>
    !x:A.
    !n:int.
      ~(x = null) /\
      (&0:int) <= n /\
      n < ntp4vc_swr_block_size mem1 x
      ==> ntp4vc_swr_accessor mem2 x n =
          ntp4vc_swr_accessor mem1 x n`;;

let ntp4vc_swr_body_pre = new_definition
 `ntp4vc_swr_body_pre
    (null:A)
    (mem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (p:A) (t:A) <=>
    ~(p = null) /\
    (t = null \/ ntp4vc_swr_black (ntp4vc_swr_colors mem t))
    ==>
    ?m:int.
      ntp4vc_swr_colors mem p =
        NTP4VC_SWR_Black (SOME m) /\
      (&0:int) <= m /\
      m < ntp4vc_swr_block_size mem p`;;

let ntp4vc_swr_body_post = new_definition
 `ntp4vc_swr_body_post
    (null:A)
    (oldmem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (oldp:A) (oldt:A)
    (newmem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (newp:A) (newt:A) <=>
    (~(oldp = null) \/
     (~(oldt = null) /\
      ~ntp4vc_swr_black (ntp4vc_swr_colors oldmem oldt))) /\
    (~(oldt = null) /\
     ~ntp4vc_swr_black (ntp4vc_swr_colors oldmem oldt) /\
     ntp4vc_swr_block_size oldmem oldt = (&0:int)
     ==>
     ntp4vc_swr_colors newmem =
       ntp4vc_swr_update
         (ntp4vc_swr_colors oldmem) oldt
         (NTP4VC_SWR_Black NONE) /\
     newt = oldt /\
     newp = oldp /\
     ntp4vc_swr_accessor newmem = ntp4vc_swr_accessor oldmem) /\
    (~(oldt = null) /\
     ~ntp4vc_swr_black (ntp4vc_swr_colors oldmem oldt) /\
     (&0:int) < ntp4vc_swr_block_size oldmem oldt
     ==>
     ntp4vc_swr_colors newmem =
       ntp4vc_swr_update
         (ntp4vc_swr_colors oldmem) oldt
         (NTP4VC_SWR_Black (SOME (&0:int))) /\
     newt = ntp4vc_swr_accessor oldmem oldt (&0:int) /\
     newp = oldt /\
     ntp4vc_swr_accessor newmem =
       ntp4vc_swr_update
         (ntp4vc_swr_accessor oldmem) oldt
         (ntp4vc_swr_update
           (ntp4vc_swr_accessor oldmem oldt)
           (&0:int) oldp)) /\
    (oldt = null \/
     ntp4vc_swr_black (ntp4vc_swr_colors oldmem oldt)
     ==>
     ?m:int.
       ntp4vc_swr_colors oldmem oldp =
         NTP4VC_SWR_Black (SOME m) /\
       let n = m + (&1:int) in
       if n = ntp4vc_swr_block_size oldmem oldp then
         newt = oldp /\
         newp = ntp4vc_swr_accessor oldmem oldp m /\
         ntp4vc_swr_colors newmem = ntp4vc_swr_colors oldmem /\
         ntp4vc_swr_accessor newmem =
           ntp4vc_swr_update
             (ntp4vc_swr_accessor oldmem) oldp
             (ntp4vc_swr_update
               (ntp4vc_swr_accessor oldmem oldp) m oldt)
       else
         newp = oldp /\
         newt = ntp4vc_swr_accessor oldmem oldp n /\
         ntp4vc_swr_colors newmem =
           ntp4vc_swr_update
             (ntp4vc_swr_colors oldmem) oldp
             (NTP4VC_SWR_Black (SOME n)) /\
         ntp4vc_swr_accessor newmem =
           ntp4vc_swr_update
             (ntp4vc_swr_accessor oldmem) oldp
             (ntp4vc_swr_update
               (ntp4vc_swr_update
                 (ntp4vc_swr_accessor oldmem oldp) n
                 (ntp4vc_swr_accessor oldmem oldp m))
               m oldt))`;;

let ntp4vc_swr_body_code = new_definition
 `ntp4vc_swr_body_code
    (null:A)
    (mem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (p:A) (t:A)
    (normal:
      ((A->int)#((A->int->A)#(A->ntp4vc_swr_color)))->A->A->bool)
    (stopped:bool) <=>
    if p = null /\
       (t = null \/ ntp4vc_swr_black (ntp4vc_swr_colors mem t))
    then stopped
    else if t = null \/
            ntp4vc_swr_black (ntp4vc_swr_colors mem t)
    then
      ~(p = null) /\
      (?m:int.
         ntp4vc_swr_colors mem p =
           NTP4VC_SWR_Black (SOME m) /\
         (&0:int) <= m /\
         m < ntp4vc_swr_block_size mem p /\
         let n = m + (&1:int) in
         if n = ntp4vc_swr_block_size mem p then
           normal
             (ntp4vc_swr_with_accessor mem
               (ntp4vc_swr_update
                 (ntp4vc_swr_accessor mem) p
                 (ntp4vc_swr_update
                   (ntp4vc_swr_accessor mem p) m t)))
             (ntp4vc_swr_accessor mem p m)
             p
         else
           n < ntp4vc_swr_block_size mem p /\
           normal
             (ntp4vc_swr_with_accessor_and_colors mem
               (ntp4vc_swr_update
                 (ntp4vc_swr_accessor mem) p
                 (ntp4vc_swr_update
                   (ntp4vc_swr_update
                     (ntp4vc_swr_accessor mem p) n
                     (ntp4vc_swr_accessor mem p m))
                   m t))
               (ntp4vc_swr_update
                 (ntp4vc_swr_colors mem) p
                 (NTP4VC_SWR_Black (SOME n))))
             p
             (ntp4vc_swr_accessor mem p n))
    else
      ~(t = null) /\
      ((&0:int) <= ntp4vc_swr_block_size mem t
       ==>
       if ntp4vc_swr_block_size mem t = (&0:int) then
         normal
           (ntp4vc_swr_with_colors mem
             (ntp4vc_swr_update
               (ntp4vc_swr_colors mem) t
               (NTP4VC_SWR_Black NONE)))
           p t
       else
         (&0:int) < ntp4vc_swr_block_size mem t /\
         normal
           (ntp4vc_swr_with_accessor_and_colors mem
             (ntp4vc_swr_update
               (ntp4vc_swr_accessor mem) t
               (ntp4vc_swr_update
                 (ntp4vc_swr_accessor mem t) (&0:int) p))
             (ntp4vc_swr_update
               (ntp4vc_swr_colors mem) t
               (NTP4VC_SWR_Black (SOME (&0:int)))))
           t
           (ntp4vc_swr_accessor mem t (&0:int)))`;;

let ntp4vc_swr_body_call_vc = new_definition
 `ntp4vc_swr_body_call_vc
    (null:A)
    (mem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (p:A) (t:A)
    (normal:
      ((A->int)#((A->int->A)#(A->ntp4vc_swr_color)))->A->A->bool)
    (stopped:bool) <=>
    ntp4vc_swr_body_pre null mem p t /\
    ntp4vc_swr_body_code null mem p t normal stopped`;;

let ntp4vc_swr_aux_pre = new_definition
 `ntp4vc_swr_aux_pre
    (null:A)
    (graph:A->bool)
    (gray:A->bool)
    (base:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (mem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (t:A) <=>
    ntp4vc_swr_well_colored_on
      null graph gray base (ntp4vc_swr_colors mem) /\
    t IN graph /\
    (!x:A.
     !n:int.
       ~(x = null) /\
       ~ntp4vc_swr_black (ntp4vc_swr_colors mem x) /\
       (&0:int) <= n /\
       n < ntp4vc_swr_block_size mem x
       ==> ntp4vc_swr_accessor mem x n =
           ntp4vc_swr_accessor base x n)`;;

let ntp4vc_swr_aux_post = new_definition
 `ntp4vc_swr_aux_post
    (null:A)
    (graph:A->bool)
    (gray:A->bool)
    (base:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (oldmem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (oldp:A) (oldt:A)
    (newmem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (newp:A) (newt:A) <=>
    newt = oldt /\
    newp = oldp /\
    ntp4vc_swr_unchanged null oldmem newmem /\
    ntp4vc_swr_well_colored_on
      null graph gray base (ntp4vc_swr_colors newmem) /\
    (ntp4vc_swr_black (ntp4vc_swr_colors newmem newt) \/
     newt = null) /\
    (!x:A.
       ~(x = null)
       ==>
       ~ntp4vc_swr_path null base newt x \/
       ntp4vc_swr_black (ntp4vc_swr_colors oldmem x)
       ==>
       ntp4vc_swr_colors newmem x =
       ntp4vc_swr_colors oldmem x)`;;

let ntp4vc_swr_variant = new_definition
 `ntp4vc_swr_variant
    (graph:A->bool) (gray:A->bool) (g2:A->bool) <=>
    (&0:int) <= (&(CARD graph):int) - (&(CARD gray):int) /\
    (&(CARD graph):int) - (&(CARD g2):int) <
    (&(CARD graph):int) - (&(CARD gray):int)`;;

let ntp4vc_swr_aux_call_vc = new_definition
 `ntp4vc_swr_aux_call_vc
    (null:A)
    (graph:A->bool)
    (gray:A->bool)
    (g2:A->bool)
    (base:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (mem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (p:A) (t:A)
    (k:((A->int)#((A->int->A)#(A->ntp4vc_swr_color)))->bool)
    <=>
    ntp4vc_swr_variant graph gray g2 /\
    ntp4vc_swr_aux_pre null graph g2 base mem t /\
    (!mem1:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)).
       ntp4vc_swr_block_size mem1 = ntp4vc_swr_block_size mem
       ==>
       ntp4vc_swr_aux_post
         null graph g2 base mem p t mem1 p t
       ==> k mem1)`;;

let ntp4vc_swr_loop_invariant = new_definition
 `ntp4vc_swr_loop_invariant
    (null:A)
    (graph:A->bool)
    (g2:A->bool)
    (base:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (entry:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (entryp:A) (entryt:A)
    (s:int) (i:int)
    (mem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (p:A) (t:A) <=>
    ntp4vc_swr_well_colored_on
      null graph g2 base (ntp4vc_swr_colors mem) /\
    p = entryt /\
    t = ntp4vc_swr_accessor base p i /\
    ntp4vc_swr_colors mem p = NTP4VC_SWR_Black (SOME i) /\
    (!j:int.
       (&0:int) <= j /\ j < s /\ ~(j = i)
       ==> ntp4vc_swr_accessor mem p j =
           ntp4vc_swr_accessor entry p j) /\
    ntp4vc_swr_accessor mem p i = entryp /\
    (!l:A.
     !n:int.
       ~(l = null) /\ ~(l = p) /\
       (&0:int) <= n /\ n < ntp4vc_swr_block_size mem l
       ==> ntp4vc_swr_accessor mem l n =
           ntp4vc_swr_accessor entry l n) /\
    (!j:int.
       (&0:int) <= j /\ j < i
       ==>
       let l = ntp4vc_swr_accessor mem p j in
       l = null \/ ntp4vc_swr_black (ntp4vc_swr_colors mem l)) /\
    (!l:A.
       ~(l = null)
       ==>
       ~ntp4vc_swr_path null base p l \/
       ntp4vc_swr_black (ntp4vc_swr_colors entry l)
       ==>
       ntp4vc_swr_colors mem l =
       ntp4vc_swr_colors entry l)`;;

let ntp4vc_swr_finish_vc = new_definition
 `ntp4vc_swr_finish_vc
    (null:A)
    (graph:A->bool)
    (gray:A->bool)
    (g2:A->bool)
    (base:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (entry:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (entryp:A) (entryt:A)
    (mem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (p:A) (t:A) <=>
    ntp4vc_swr_aux_call_vc
      null graph gray g2 base mem p t
      (\mem1.
         ntp4vc_swr_body_call_vc
           null mem1 p t
           (\mem2 p2 t2.
              p2 = entryp /\
              t2 = entryt /\
              ntp4vc_swr_aux_post
                null graph gray base
                entry entryp entryt mem2 p2 t2)
           F)`;;

let ntp4vc_swr_loop_vc = new_definition
 `ntp4vc_swr_loop_vc
    (null:A)
    (graph:A->bool)
    (gray:A->bool)
    (g2:A->bool)
    (base:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (entry:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (entryp:A) (entryt:A)
    (s:int)
    (first:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (firstp:A) (firstt:A) <=>
    ((&0:int) <= s - (&1:int)
     ==>
     ntp4vc_swr_loop_invariant
       null graph g2 base entry entryp entryt s (&0:int)
       first firstp firstt) /\
    (!mem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)).
     !p t:A.
     !i:int.
       ntp4vc_swr_block_size mem = ntp4vc_swr_block_size entry /\
       (&0:int) <= i /\ i <= s - (&2:int) /\
       ntp4vc_swr_loop_invariant
         null graph g2 base entry entryp entryt s i mem p t
       ==>
       ntp4vc_swr_aux_call_vc
         null graph gray g2 base mem p t
         (\mem1.
            ntp4vc_swr_body_call_vc
              null mem1 p t
              (\mem2 p2 t2.
                 ntp4vc_swr_loop_invariant
                   null graph g2 base entry entryp entryt
                   s (i + (&1:int)) mem2 p2 t2)
              F)) /\
    (!mem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)).
     !p t:A.
       ntp4vc_swr_block_size mem = ntp4vc_swr_block_size entry /\
       ntp4vc_swr_loop_invariant
         null graph g2 base entry entryp entryt
         s (s - (&1:int)) mem p t
       ==>
       ntp4vc_swr_finish_vc
         null graph gray g2 base entry entryp entryt mem p t) /\
    (s - (&1:int) < (&0:int)
     ==>
     ntp4vc_swr_finish_vc
       null graph gray g2 base entry entryp entryt
       first firstp firstt)`;;

let ntp4vc_swr_aux_code_vc = new_definition
 `ntp4vc_swr_aux_code_vc
    (null:A)
    (graph:A->bool)
    (gray:A->bool)
    (base:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (mem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (p:A) (t:A) <=>
    if t = null \/ ntp4vc_swr_black (ntp4vc_swr_colors mem t)
    then
      ntp4vc_swr_aux_post
        null graph gray base mem p t mem p t
    else
      ~(t = null) /\
      ((&0:int) <= ntp4vc_swr_block_size mem t
       ==>
       let s = ntp4vc_swr_block_size mem t in
       let g2 = t INSERT gray in
       ntp4vc_swr_body_call_vc
         null mem p t
         (\mem1 p1 t1.
            if ~(s = (&0:int)) then
              ntp4vc_swr_loop_vc
                null graph gray g2 base mem p t s mem1 p1 t1
            else
              ntp4vc_swr_aux_post
                null graph gray base mem p t mem1 p1 t1)
         F)`;;

let ntp4vc_swr_body_impl_vc = new_definition
 `ntp4vc_swr_body_impl_vc
    (null:A)
    (base:(A->int)#((A->int->A)#(A->ntp4vc_swr_color))) <=>
    !mem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)).
    !p t:A.
      ntp4vc_swr_block_size mem = ntp4vc_swr_block_size base
      ==>
      ntp4vc_swr_body_pre null mem p t
      ==>
      ntp4vc_swr_body_code
        null mem p t
        (ntp4vc_swr_body_post null mem p t)
        (p = null /\
         (t = null \/ ntp4vc_swr_black (ntp4vc_swr_colors mem t)))`;;

let ntp4vc_swr_aux_impl_vc = new_definition
 `ntp4vc_swr_aux_impl_vc
    (null:A)
    (graph:A->bool)
    (base:(A->int)#((A->int->A)#(A->ntp4vc_swr_color))) <=>
    !mem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)).
    !p t:A.
      ntp4vc_swr_block_size mem = ntp4vc_swr_block_size base
      ==>
      !gray:A->bool.
        ntp4vc_swr_aux_pre null graph gray base mem t
        ==>
        ntp4vc_swr_aux_code_vc
          null graph gray base mem p t`;;

let ntp4vc_swr_final_post = new_definition
 `ntp4vc_swr_final_post
    (null:A)
    (root:A)
    (base:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)))
    (mem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color))) <=>
    ntp4vc_swr_unchanged null base mem /\
    (!x:A.
       ntp4vc_swr_path null base root x /\ ~(x = null)
       ==> ntp4vc_swr_black (ntp4vc_swr_colors mem x)) /\
    (!x:A.
       ~ntp4vc_swr_path null base root x /\ ~(x = null)
       ==> ntp4vc_swr_colors mem x =
           ntp4vc_swr_colors base x)`;;

let ntp4vc_swr_main_vc = new_definition
 `ntp4vc_swr_main_vc
    (null:A)
    (root:A)
    (graph:A->bool)
    (base:(A->int)#((A->int->A)#(A->ntp4vc_swr_color))) <=>
    ntp4vc_swr_aux_pre null graph {} base base root /\
    (!mem:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)).
       ntp4vc_swr_block_size mem = ntp4vc_swr_block_size base
       ==>
       ntp4vc_swr_aux_post
         null graph {} base base null root mem null root
       ==>
       ntp4vc_swr_body_call_vc
         null mem null root
         (\mem1 p t. F)
         (ntp4vc_swr_final_post null root base mem))`;;

let statement =
 `!null:A.
  !root:A.
  !graph:A->bool.
  !memo:(A->int)#((A->int->A)#(A->ntp4vc_swr_color)).
    FINITE graph
    ==>
    root IN graph
    ==>
    (!l:A.
     !n:int.
       l IN graph /\
       ~(l = null) /\
       (&0:int) <= n /\
       n < ntp4vc_swr_block_size memo l
       ==> ntp4vc_swr_accessor memo l n IN graph)
    ==>
    (!x:A.
       x IN graph
       ==> ~ntp4vc_swr_black (ntp4vc_swr_colors memo x))
    ==>
    ntp4vc_swr_body_impl_vc null memo /\
    ntp4vc_swr_aux_impl_vc null graph memo /\
    ntp4vc_swr_main_vc null root graph memo`;;
