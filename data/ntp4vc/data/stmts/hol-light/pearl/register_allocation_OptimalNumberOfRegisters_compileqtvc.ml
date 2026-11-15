(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/register_allocation_OptimalNumberOfRegisters_compileqtvc: the
  expression compiler verification condition using the recursively computed
  minimal register requirement to choose evaluation order, with stack
  spilling when registers are exhausted. This file contains no proof.
*)

new_type ("ntp4vc_onr_addr",0);;

let ntp4vc_onr_expr_INDUCT,ntp4vc_onr_expr_RECURSION =
  define_type
   "ntp4vc_onr_expr =
      NTP4VC_ONR_Evar ntp4vc_onr_addr
    | NTP4VC_ONR_Eneg ntp4vc_onr_expr
    | NTP4VC_ONR_Eadd ntp4vc_onr_expr ntp4vc_onr_expr";;

let ntp4vc_onr_instr_INDUCT,ntp4vc_onr_instr_RECURSION =
  define_type
   "ntp4vc_onr_instr =
      NTP4VC_ONR_Iload ntp4vc_onr_addr int
    | NTP4VC_ONR_Ineg int
    | NTP4VC_ONR_Iadd int int
    | NTP4VC_ONR_Ipush int
    | NTP4VC_ONR_Ipop int";;

let ntp4vc_onr_state_INDUCT,ntp4vc_onr_state_RECURSION =
  define_type
   "ntp4vc_onr_state =
      NTP4VC_ONR_State
        (ntp4vc_onr_addr->int) (int->int) (int list)";;

let ntp4vc_onr_mem =
  new_recursive_definition ntp4vc_onr_state_RECURSION
   `ntp4vc_onr_mem (NTP4VC_ONR_State mem reg st) = mem`;;

let ntp4vc_onr_reg =
  new_recursive_definition ntp4vc_onr_state_RECURSION
   `ntp4vc_onr_reg (NTP4VC_ONR_State mem reg st) = reg`;;

let ntp4vc_onr_stack =
  new_recursive_definition ntp4vc_onr_state_RECURSION
   `ntp4vc_onr_stack (NTP4VC_ONR_State mem reg st) = st`;;

let ntp4vc_onr_eval =
  new_recursive_definition ntp4vc_onr_expr_RECURSION
   `(!mem:ntp4vc_onr_addr->int.
     !x:ntp4vc_onr_addr.
       ntp4vc_onr_eval mem (NTP4VC_ONR_Evar x) = mem x) /\
    (!mem:ntp4vc_onr_addr->int.
     !e:ntp4vc_onr_expr.
       ntp4vc_onr_eval mem (NTP4VC_ONR_Eneg e) =
       --(ntp4vc_onr_eval mem e)) /\
    (!mem:ntp4vc_onr_addr->int.
     !e1 e2:ntp4vc_onr_expr.
       ntp4vc_onr_eval mem (NTP4VC_ONR_Eadd e1 e2) =
       ntp4vc_onr_eval mem e1 + ntp4vc_onr_eval mem e2)`;;

let ntp4vc_onr_update = new_definition
 `ntp4vc_onr_update (reg:int->int) (r:int) (v:int) =
    \r':int. if r' = r then v else reg r'`;;

let ntp4vc_onr_exec =
  new_recursive_definition ntp4vc_onr_instr_RECURSION
   `(!x:ntp4vc_onr_addr.
     !r:int.
     !s:ntp4vc_onr_state.
       ntp4vc_onr_exec (NTP4VC_ONR_Iload x r) s =
       NTP4VC_ONR_State
         (ntp4vc_onr_mem s)
         (ntp4vc_onr_update
           (ntp4vc_onr_reg s) r (ntp4vc_onr_mem s x))
         (ntp4vc_onr_stack s)) /\
    (!r:int.
     !s:ntp4vc_onr_state.
       ntp4vc_onr_exec (NTP4VC_ONR_Ineg r) s =
       NTP4VC_ONR_State
         (ntp4vc_onr_mem s)
         (ntp4vc_onr_update
           (ntp4vc_onr_reg s) r (--(ntp4vc_onr_reg s r)))
         (ntp4vc_onr_stack s)) /\
    (!r1 r2:int.
     !s:ntp4vc_onr_state.
       ntp4vc_onr_exec (NTP4VC_ONR_Iadd r1 r2) s =
       NTP4VC_ONR_State
         (ntp4vc_onr_mem s)
         (ntp4vc_onr_update
           (ntp4vc_onr_reg s) r2
           (ntp4vc_onr_reg s r1 + ntp4vc_onr_reg s r2))
         (ntp4vc_onr_stack s)) /\
    (!r:int.
     !s:ntp4vc_onr_state.
       ntp4vc_onr_exec (NTP4VC_ONR_Ipush r) s =
       NTP4VC_ONR_State
         (ntp4vc_onr_mem s)
         (ntp4vc_onr_reg s)
         (CONS (ntp4vc_onr_reg s r) (ntp4vc_onr_stack s))) /\
    (!r:int.
     !s:ntp4vc_onr_state.
       ntp4vc_onr_exec (NTP4VC_ONR_Ipop r) s =
       if ntp4vc_onr_stack s = [] then
         s
       else
         NTP4VC_ONR_State
           (ntp4vc_onr_mem s)
           (ntp4vc_onr_update
             (ntp4vc_onr_reg s) r (HD (ntp4vc_onr_stack s)))
           (TL (ntp4vc_onr_stack s)))`;;

let ntp4vc_onr_exec_list =
  new_recursive_definition list_RECURSION
   `(!s:ntp4vc_onr_state.
       ntp4vc_onr_exec_list ([]:ntp4vc_onr_instr list) s = s) /\
    (!i:ntp4vc_onr_instr.
     !code:ntp4vc_onr_instr list.
     !s:ntp4vc_onr_state.
       ntp4vc_onr_exec_list (CONS i code) s =
       ntp4vc_onr_exec_list code (ntp4vc_onr_exec i s))`;;

let ntp4vc_onr_expr_post = new_definition
 `ntp4vc_onr_expr_post
    (e:ntp4vc_onr_expr) (r:int)
    (s:ntp4vc_onr_state) (s':ntp4vc_onr_state) <=>
    ntp4vc_onr_mem s' = ntp4vc_onr_mem s /\
    ntp4vc_onr_reg s' r = ntp4vc_onr_eval (ntp4vc_onr_mem s) e /\
    ntp4vc_onr_stack s' = ntp4vc_onr_stack s /\
    (!r':int.
       r' < r ==> ntp4vc_onr_reg s' r' = ntp4vc_onr_reg s r')`;;

let ntp4vc_onr_hcode_INDUCT,ntp4vc_onr_hcode_RECURSION =
  define_type
   "ntp4vc_onr_hcode =
      NTP4VC_ONR_Hcode
        (ntp4vc_onr_instr list)
        (ntp4vc_onr_state->ntp4vc_onr_state->bool)";;

let ntp4vc_onr_wcode_INDUCT,ntp4vc_onr_wcode_RECURSION =
  define_type
   "ntp4vc_onr_wcode =
      NTP4VC_ONR_Wcode
        ((ntp4vc_onr_state->bool)->ntp4vc_onr_state->bool)
        (ntp4vc_onr_instr list)";;

let ntp4vc_onr_hpost =
  new_recursive_definition ntp4vc_onr_hcode_RECURSION
   `ntp4vc_onr_hpost (NTP4VC_ONR_Hcode code pst) = pst`;;

let ntp4vc_onr_hcode_body =
  new_recursive_definition ntp4vc_onr_hcode_RECURSION
   `ntp4vc_onr_hcode_body (NTP4VC_ONR_Hcode code pst) = code`;;

let ntp4vc_onr_wtrans =
  new_recursive_definition ntp4vc_onr_wcode_RECURSION
   `ntp4vc_onr_wtrans (NTP4VC_ONR_Wcode trans code) = trans`;;

let ntp4vc_onr_wcode_body =
  new_recursive_definition ntp4vc_onr_wcode_RECURSION
   `ntp4vc_onr_wcode_body (NTP4VC_ONR_Wcode trans code) = code`;;

let ntp4vc_onr_hcode_ok = new_definition
 `ntp4vc_onr_hcode_ok (hc:ntp4vc_onr_hcode) <=>
    !s:ntp4vc_onr_state.
      ntp4vc_onr_hpost hc s
        (ntp4vc_onr_exec_list (ntp4vc_onr_hcode_body hc) s)`;;

let ntp4vc_onr_wcode_ok = new_definition
 `ntp4vc_onr_wcode_ok (wc:ntp4vc_onr_wcode) <=>
    !q:ntp4vc_onr_state->bool.
    !s:ntp4vc_onr_state.
      ntp4vc_onr_wtrans wc q s
      ==> q (ntp4vc_onr_exec_list (ntp4vc_onr_wcode_body wc) s)`;;

let ntp4vc_onr_to_wp = new_definition
 `ntp4vc_onr_to_wp
    (pst:ntp4vc_onr_state->ntp4vc_onr_state->bool)
    (q:ntp4vc_onr_state->bool) (s1:ntp4vc_onr_state) <=>
    !s2:ntp4vc_onr_state. pst s1 s2 ==> q s2`;;

let ntp4vc_onr_rcompose = new_definition
 `ntp4vc_onr_rcompose (f:A->B) (g:B->C) (x:A) = g (f x)`;;

let ntp4vc_onr_identity = new_definition
 `ntp4vc_onr_identity (y:ntp4vc_onr_state->bool) = y`;;

let ntp4vc_onr_exec_closure = new_definition
 `ntp4vc_onr_exec_closure
    (i:ntp4vc_onr_instr) (s:ntp4vc_onr_state) =
    ntp4vc_onr_exec i s`;;

let ntp4vc_onr_n =
  new_recursive_definition ntp4vc_onr_expr_RECURSION
   `(!x:ntp4vc_onr_addr.
       ntp4vc_onr_n (NTP4VC_ONR_Evar x) = (&1:int)) /\
    (!e:ntp4vc_onr_expr.
       ntp4vc_onr_n (NTP4VC_ONR_Eneg e) = ntp4vc_onr_n e) /\
    (!e1 e2:ntp4vc_onr_expr.
       ntp4vc_onr_n (NTP4VC_ONR_Eadd e1 e2) =
       let n1 = ntp4vc_onr_n e1 in
       let n2 = ntp4vc_onr_n e2 in
       if n1 = n2 then (&1:int) + n1
       else if n1 <= n2 then n2 else n1)`;;

let ntp4vc_onr_measure =
  new_recursive_definition ntp4vc_onr_expr_RECURSION
   `(!x:ntp4vc_onr_addr.
       ntp4vc_onr_measure (NTP4VC_ONR_Evar x) = (&0:int)) /\
    (!e:ntp4vc_onr_expr.
       ntp4vc_onr_measure (NTP4VC_ONR_Eneg e) =
       (&1:int) + ntp4vc_onr_measure e) /\
    (!e1 e2:ntp4vc_onr_expr.
       ntp4vc_onr_measure (NTP4VC_ONR_Eadd e1 e2) =
       (&1:int) +
       if ntp4vc_onr_n e2 <= ntp4vc_onr_n e1
       then ntp4vc_onr_measure e1 + ntp4vc_onr_measure e2
       else (&1:int) +
            ntp4vc_onr_measure e1 + ntp4vc_onr_measure e2)`;;

let ntp4vc_onr_measure_decrease = new_definition
 `ntp4vc_onr_measure_decrease
    (whole:ntp4vc_onr_expr) (recursive_argument:ntp4vc_onr_expr) <=>
    (&0:int) <= ntp4vc_onr_measure whole /\
    ntp4vc_onr_measure recursive_argument < ntp4vc_onr_measure whole`;;

let ntp4vc_onr_compile_pre_add = new_definition
 `ntp4vc_onr_compile_pre_add
    (k:int) (r:int) (e1:ntp4vc_onr_expr) (e2:ntp4vc_onr_expr) <=>
    COND (r < k - (&1:int))
         (!o2:ntp4vc_onr_wcode.
           ntp4vc_onr_wcode_ok o2 /\
           ntp4vc_onr_wtrans o2 = ntp4vc_onr_identity
           ==>
           ntp4vc_onr_wcode_ok o2 /\
           (!o3:ntp4vc_onr_wcode.
              ntp4vc_onr_wcode_ok o3 /\
              ntp4vc_onr_wtrans o3 =
                ntp4vc_onr_rcompose
                  (ntp4vc_onr_wtrans o2)
                  (ntp4vc_onr_rcompose
                    (ntp4vc_onr_exec_closure
                      (NTP4VC_ONR_Iadd (r + (&1:int)) r)))
              ==>
              let o4 = r + (&1:int) in
              (ntp4vc_onr_measure_decrease
                 (NTP4VC_ONR_Eadd e1 e2) e2 /\
               (&0:int) <= o4 /\ o4 < k) /\
              (!o5:ntp4vc_onr_hcode.
                 ntp4vc_onr_hcode_ok o5 /\
                 ntp4vc_onr_hpost o5 = ntp4vc_onr_expr_post e2 o4
                 ==>
                 ntp4vc_onr_hcode_ok o5 /\
                 (!o6:ntp4vc_onr_wcode.
                    ntp4vc_onr_wcode_ok o6 /\
                    ntp4vc_onr_wtrans o6 =
                      ntp4vc_onr_to_wp (ntp4vc_onr_hpost o5)
                    ==>
                    (ntp4vc_onr_measure_decrease
                       (NTP4VC_ONR_Eadd e1 e2) e1 /\
                     (&0:int) <= r /\ r < k) /\
                    (!o7:ntp4vc_onr_hcode.
                       ntp4vc_onr_hcode_ok o7 /\
                       ntp4vc_onr_hpost o7 =
                         ntp4vc_onr_expr_post e1 r
                       ==>
                       ntp4vc_onr_hcode_ok o7 /\
                       (!o8:ntp4vc_onr_wcode.
                          ntp4vc_onr_wcode_ok o8 /\
                          ntp4vc_onr_wtrans o8 =
                            ntp4vc_onr_to_wp
                              (ntp4vc_onr_hpost o7)
                          ==>
                          (ntp4vc_onr_wcode_ok o8 /\
                           ntp4vc_onr_wcode_ok o6) /\
                          (!o9:ntp4vc_onr_wcode.
                             ntp4vc_onr_wcode_ok o9 /\
                             ntp4vc_onr_wtrans o9 =
                               ntp4vc_onr_rcompose
                                 (ntp4vc_onr_wtrans o6)
                                 (ntp4vc_onr_wtrans o8)
                             ==>
                             ntp4vc_onr_wcode_ok o9 /\
                             ntp4vc_onr_wcode_ok o3)))))))
         (!o2:ntp4vc_onr_wcode.
           ntp4vc_onr_wcode_ok o2 /\
           ntp4vc_onr_wtrans o2 = ntp4vc_onr_identity
           ==>
           ntp4vc_onr_wcode_ok o2 /\
           (!o3:ntp4vc_onr_wcode.
              ntp4vc_onr_wcode_ok o3 /\
              ntp4vc_onr_wtrans o3 =
                ntp4vc_onr_rcompose
                  (ntp4vc_onr_wtrans o2)
                  (ntp4vc_onr_rcompose
                    (ntp4vc_onr_exec_closure
                      (NTP4VC_ONR_Ipop (k - (&2:int)))))
              ==>
              ntp4vc_onr_wcode_ok o3 /\
              (!o4:ntp4vc_onr_wcode.
                 ntp4vc_onr_wcode_ok o4 /\
                 ntp4vc_onr_wtrans o4 =
                   ntp4vc_onr_rcompose
                     (ntp4vc_onr_wtrans o3)
                     (ntp4vc_onr_rcompose
                       (ntp4vc_onr_exec_closure
                         (NTP4VC_ONR_Iadd
                           (k - (&2:int)) (k - (&1:int)))))
                 ==>
                 let o5 = k - (&1:int) in
                 (ntp4vc_onr_measure_decrease
                    (NTP4VC_ONR_Eadd e1 e2) e2 /\
                  (&0:int) <= o5 /\ o5 < k) /\
                 (!o6:ntp4vc_onr_hcode.
                    ntp4vc_onr_hcode_ok o6 /\
                    ntp4vc_onr_hpost o6 =
                      ntp4vc_onr_expr_post e2 o5
                    ==>
                    ntp4vc_onr_hcode_ok o6 /\
                    (!o7:ntp4vc_onr_wcode.
                       ntp4vc_onr_wcode_ok o7 /\
                       ntp4vc_onr_wtrans o7 =
                         ntp4vc_onr_to_wp (ntp4vc_onr_hpost o6)
                       ==>
                       let o8 = k - (&2:int) in
                       (ntp4vc_onr_measure_decrease
                          (NTP4VC_ONR_Eadd e1 e2) e1 /\
                        (&0:int) <= o8 /\ o8 < k) /\
                       (!o9:ntp4vc_onr_hcode.
                          ntp4vc_onr_hcode_ok o9 /\
                          ntp4vc_onr_hpost o9 =
                            ntp4vc_onr_expr_post e1 o8
                          ==>
                          ntp4vc_onr_hcode_ok o9 /\
                          (!o10:ntp4vc_onr_wcode.
                             ntp4vc_onr_wcode_ok o10 /\
                             ntp4vc_onr_wtrans o10 =
                               ntp4vc_onr_to_wp
                                 (ntp4vc_onr_hpost o9)
                             ==>
                             (ntp4vc_onr_wcode_ok o10 /\
                              ntp4vc_onr_wcode_ok o7) /\
                             (!o11:ntp4vc_onr_wcode.
                                ntp4vc_onr_wcode_ok o11 /\
                                ntp4vc_onr_wtrans o11 =
                                  ntp4vc_onr_rcompose
                                    (ntp4vc_onr_wtrans o7)
                                    (ntp4vc_onr_wtrans o10)
                                ==>
                                (ntp4vc_onr_wcode_ok o11 /\
                                 ntp4vc_onr_wcode_ok o4) /\
                                (!o12:ntp4vc_onr_wcode.
                                   ntp4vc_onr_wcode_ok o12 /\
                                   ntp4vc_onr_wtrans o12 =
                                     ntp4vc_onr_rcompose
                                       (ntp4vc_onr_wtrans o4)
                                       (ntp4vc_onr_wtrans o11)
                                   ==>
                                   ntp4vc_onr_wcode_ok o12)))))))))`;;

let ntp4vc_onr_compile_pre_swapped = new_definition
 `ntp4vc_onr_compile_pre_swapped
    (k:int) (r:int) (e1:ntp4vc_onr_expr) (e2:ntp4vc_onr_expr) <=>
    (ntp4vc_onr_measure_decrease
       (NTP4VC_ONR_Eadd e1 e2) (NTP4VC_ONR_Eadd e2 e1) /\
     (&0:int) <= r /\ r < k) /\
    (!o3:ntp4vc_onr_hcode.
       ntp4vc_onr_hcode_ok o3 /\
       ntp4vc_onr_hpost o3 =
         ntp4vc_onr_expr_post (NTP4VC_ONR_Eadd e2 e1) r
       ==>
       ntp4vc_onr_hcode_ok o3)`;;

let ntp4vc_onr_compile_pre =
  new_recursive_definition ntp4vc_onr_expr_RECURSION
   `(!k r:int.
     !x:ntp4vc_onr_addr.
       ntp4vc_onr_compile_pre k r (NTP4VC_ONR_Evar x) <=>
       (!o2:ntp4vc_onr_wcode.
          ntp4vc_onr_wcode_ok o2 /\
          ntp4vc_onr_wtrans o2 = ntp4vc_onr_identity
          ==> ntp4vc_onr_wcode_ok o2)) /\
    (!k r:int.
     !e1:ntp4vc_onr_expr.
       ntp4vc_onr_compile_pre k r (NTP4VC_ONR_Eneg e1) <=>
       (!o2:ntp4vc_onr_wcode.
          ntp4vc_onr_wcode_ok o2 /\
          ntp4vc_onr_wtrans o2 = ntp4vc_onr_identity
          ==>
          ntp4vc_onr_wcode_ok o2 /\
          (!o3:ntp4vc_onr_wcode.
             ntp4vc_onr_wcode_ok o3 /\
             ntp4vc_onr_wtrans o3 =
               ntp4vc_onr_rcompose
                 (ntp4vc_onr_wtrans o2)
                 (ntp4vc_onr_rcompose
                   (ntp4vc_onr_exec_closure
                     (NTP4VC_ONR_Ineg r)))
             ==>
             (ntp4vc_onr_measure_decrease
                (NTP4VC_ONR_Eneg e1) e1 /\
              (&0:int) <= r /\ r < k) /\
             (!o4:ntp4vc_onr_hcode.
                ntp4vc_onr_hcode_ok o4 /\
                ntp4vc_onr_hpost o4 = ntp4vc_onr_expr_post e1 r
                ==>
                ntp4vc_onr_hcode_ok o4 /\
                (!o5:ntp4vc_onr_wcode.
                   ntp4vc_onr_wcode_ok o5 /\
                   ntp4vc_onr_wtrans o5 =
                     ntp4vc_onr_to_wp (ntp4vc_onr_hpost o4)
                   ==>
                   ntp4vc_onr_wcode_ok o5 /\
                   ntp4vc_onr_wcode_ok o3))))) /\
    (!k r:int.
     !e1 e2:ntp4vc_onr_expr.
       ntp4vc_onr_compile_pre k r (NTP4VC_ONR_Eadd e1 e2) <=>
       COND (ntp4vc_onr_n e2 <= ntp4vc_onr_n e1)
            (ntp4vc_onr_compile_pre_add k r e1 e2)
            (ntp4vc_onr_compile_pre_swapped k r e1 e2))`;;

let ntp4vc_onr_compile_build_add = new_definition
 `ntp4vc_onr_compile_build_add
    (k:int) (r:int) (e1:ntp4vc_onr_expr) (e2:ntp4vc_onr_expr)
    (o2:ntp4vc_onr_wcode) <=>
    COND (r < k - (&1:int))
         (?o3:ntp4vc_onr_wcode.
           (ntp4vc_onr_wcode_ok o3 /\
            ntp4vc_onr_wtrans o3 = ntp4vc_onr_identity) /\
           (?o4:ntp4vc_onr_wcode.
              (ntp4vc_onr_wcode_ok o4 /\
               ntp4vc_onr_wtrans o4 =
                 ntp4vc_onr_rcompose
                   (ntp4vc_onr_wtrans o3)
                   (ntp4vc_onr_rcompose
                     (ntp4vc_onr_exec_closure
                       (NTP4VC_ONR_Iadd (r + (&1:int)) r)))) /\
              (?o5:ntp4vc_onr_hcode.
                 (ntp4vc_onr_hcode_ok o5 /\
                  ntp4vc_onr_hpost o5 =
                    ntp4vc_onr_expr_post e2 (r + (&1:int))) /\
                 (?o6:ntp4vc_onr_wcode.
                    (ntp4vc_onr_wcode_ok o6 /\
                     ntp4vc_onr_wtrans o6 =
                       ntp4vc_onr_to_wp (ntp4vc_onr_hpost o5)) /\
                    (?o7:ntp4vc_onr_hcode.
                       (ntp4vc_onr_hcode_ok o7 /\
                        ntp4vc_onr_hpost o7 =
                          ntp4vc_onr_expr_post e1 r) /\
                       (?o8:ntp4vc_onr_wcode.
                          (ntp4vc_onr_wcode_ok o8 /\
                           ntp4vc_onr_wtrans o8 =
                             ntp4vc_onr_to_wp
                               (ntp4vc_onr_hpost o7)) /\
                          (?o9:ntp4vc_onr_wcode.
                             (ntp4vc_onr_wcode_ok o9 /\
                              ntp4vc_onr_wtrans o9 =
                                ntp4vc_onr_rcompose
                                  (ntp4vc_onr_wtrans o6)
                                  (ntp4vc_onr_wtrans o8)) /\
                             ntp4vc_onr_wcode_ok o2 /\
                             ntp4vc_onr_wtrans o2 =
                               ntp4vc_onr_rcompose
                                 (ntp4vc_onr_wtrans o4)
                                 (ntp4vc_onr_wtrans o9))))))))
         (?o3:ntp4vc_onr_wcode.
           (ntp4vc_onr_wcode_ok o3 /\
            ntp4vc_onr_wtrans o3 = ntp4vc_onr_identity) /\
           (?o4:ntp4vc_onr_wcode.
              (ntp4vc_onr_wcode_ok o4 /\
               ntp4vc_onr_wtrans o4 =
                 ntp4vc_onr_rcompose
                   (ntp4vc_onr_wtrans o3)
                   (ntp4vc_onr_rcompose
                     (ntp4vc_onr_exec_closure
                       (NTP4VC_ONR_Ipop (k - (&2:int)))))) /\
              (?o5:ntp4vc_onr_wcode.
                 (ntp4vc_onr_wcode_ok o5 /\
                  ntp4vc_onr_wtrans o5 =
                    ntp4vc_onr_rcompose
                      (ntp4vc_onr_wtrans o4)
                      (ntp4vc_onr_rcompose
                        (ntp4vc_onr_exec_closure
                          (NTP4VC_ONR_Iadd
                            (k - (&2:int)) (k - (&1:int)))))) /\
                 (?o6:ntp4vc_onr_hcode.
                    (ntp4vc_onr_hcode_ok o6 /\
                     ntp4vc_onr_hpost o6 =
                       ntp4vc_onr_expr_post e2 (k - (&1:int))) /\
                    (?o7:ntp4vc_onr_wcode.
                       (ntp4vc_onr_wcode_ok o7 /\
                        ntp4vc_onr_wtrans o7 =
                          ntp4vc_onr_to_wp (ntp4vc_onr_hpost o6)) /\
                       (?o8:ntp4vc_onr_hcode.
                          (ntp4vc_onr_hcode_ok o8 /\
                           ntp4vc_onr_hpost o8 =
                             ntp4vc_onr_expr_post
                               e1 (k - (&2:int))) /\
                          (?o9:ntp4vc_onr_wcode.
                             (ntp4vc_onr_wcode_ok o9 /\
                              ntp4vc_onr_wtrans o9 =
                                ntp4vc_onr_to_wp
                                  (ntp4vc_onr_hpost o8)) /\
                             (?o10:ntp4vc_onr_wcode.
                                (ntp4vc_onr_wcode_ok o10 /\
                                 ntp4vc_onr_wtrans o10 =
                                   ntp4vc_onr_rcompose
                                     (ntp4vc_onr_wtrans o7)
                                     (ntp4vc_onr_wtrans o9)) /\
                                (?o11:ntp4vc_onr_wcode.
                                   (ntp4vc_onr_wcode_ok o11 /\
                                    ntp4vc_onr_wtrans o11 =
                                      ntp4vc_onr_rcompose
                                        (ntp4vc_onr_wtrans o5)
                                        (ntp4vc_onr_wtrans o10)) /\
                                   ntp4vc_onr_wcode_ok o2 /\
                                   ntp4vc_onr_wtrans o2 =
                                     ntp4vc_onr_rcompose
                                       (ntp4vc_onr_wtrans o11)
                                       (ntp4vc_onr_rcompose
                                         (ntp4vc_onr_exec_closure
                                           (NTP4VC_ONR_Ipush
                                             (k - (&2:int))))))))))))))`;;

let ntp4vc_onr_compile_build_swapped = new_definition
 `ntp4vc_onr_compile_build_swapped
    (r:int) (e1:ntp4vc_onr_expr) (e2:ntp4vc_onr_expr)
    (o2:ntp4vc_onr_wcode) <=>
    ?o3:ntp4vc_onr_hcode.
      (ntp4vc_onr_hcode_ok o3 /\
       ntp4vc_onr_hpost o3 =
         ntp4vc_onr_expr_post (NTP4VC_ONR_Eadd e2 e1) r) /\
      ntp4vc_onr_wcode_ok o2 /\
      ntp4vc_onr_wtrans o2 =
        ntp4vc_onr_to_wp (ntp4vc_onr_hpost o3)`;;

let ntp4vc_onr_compile_build =
  new_recursive_definition ntp4vc_onr_expr_RECURSION
   `(!k r:int.
     !x:ntp4vc_onr_addr.
     !o2:ntp4vc_onr_wcode.
       ntp4vc_onr_compile_build k r (NTP4VC_ONR_Evar x) o2 <=>
       ?o3:ntp4vc_onr_wcode.
         (ntp4vc_onr_wcode_ok o3 /\
          ntp4vc_onr_wtrans o3 = ntp4vc_onr_identity) /\
         ntp4vc_onr_wcode_ok o2 /\
         ntp4vc_onr_wtrans o2 =
           ntp4vc_onr_rcompose
             (ntp4vc_onr_wtrans o3)
             (ntp4vc_onr_rcompose
               (ntp4vc_onr_exec_closure
                 (NTP4VC_ONR_Iload x r)))) /\
    (!k r:int.
     !e1:ntp4vc_onr_expr.
     !o2:ntp4vc_onr_wcode.
       ntp4vc_onr_compile_build k r (NTP4VC_ONR_Eneg e1) o2 <=>
       ?o3:ntp4vc_onr_wcode.
         (ntp4vc_onr_wcode_ok o3 /\
          ntp4vc_onr_wtrans o3 = ntp4vc_onr_identity) /\
         (?o4:ntp4vc_onr_wcode.
            (ntp4vc_onr_wcode_ok o4 /\
             ntp4vc_onr_wtrans o4 =
               ntp4vc_onr_rcompose
                 (ntp4vc_onr_wtrans o3)
                 (ntp4vc_onr_rcompose
                   (ntp4vc_onr_exec_closure
                     (NTP4VC_ONR_Ineg r)))) /\
            (?o5:ntp4vc_onr_hcode.
               (ntp4vc_onr_hcode_ok o5 /\
                ntp4vc_onr_hpost o5 = ntp4vc_onr_expr_post e1 r) /\
               (?o6:ntp4vc_onr_wcode.
                  (ntp4vc_onr_wcode_ok o6 /\
                   ntp4vc_onr_wtrans o6 =
                     ntp4vc_onr_to_wp (ntp4vc_onr_hpost o5)) /\
                  ntp4vc_onr_wcode_ok o2 /\
                  ntp4vc_onr_wtrans o2 =
                    ntp4vc_onr_rcompose
                      (ntp4vc_onr_wtrans o4)
                      (ntp4vc_onr_wtrans o6))))) /\
    (!k r:int.
     !e1 e2:ntp4vc_onr_expr.
     !o2:ntp4vc_onr_wcode.
       ntp4vc_onr_compile_build k r (NTP4VC_ONR_Eadd e1 e2) o2 <=>
       COND (ntp4vc_onr_n e2 <= ntp4vc_onr_n e1)
            (ntp4vc_onr_compile_build_add k r e1 e2 o2)
            (ntp4vc_onr_compile_build_swapped r e1 e2 o2))`;;

let statement =
 `!k:int.
    (&2:int) <= k
    ==>
    !r:int.
    !e:ntp4vc_onr_expr.
      (&0:int) <= r
      ==>
      r < k
      ==>
      ntp4vc_onr_compile_pre k r e /\
      (!o2:ntp4vc_onr_wcode.
         ntp4vc_onr_compile_build k r e o2
         ==>
         (ntp4vc_onr_wcode_ok o2 /\
          (!x:ntp4vc_onr_state.
             ntp4vc_onr_wtrans o2
               (ntp4vc_onr_expr_post e r x) x)) /\
         (!result:ntp4vc_onr_hcode.
            ntp4vc_onr_hcode_ok result /\
            ntp4vc_onr_hpost result = ntp4vc_onr_expr_post e r
            ==>
            ntp4vc_onr_hcode_ok result /\
            ntp4vc_onr_hpost result = ntp4vc_onr_expr_post e r))`;;
