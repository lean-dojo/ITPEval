(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/register_allocation_FiniteNumberOfRegisters_compileqtvc: the
  finite-register expression compiler verification condition, including
  direct register allocation, stack spilling, and double-WP correctness.
  This file contains no proof.
*)

new_type ("ntp4vc_fra_addr",0);;

let ntp4vc_fra_expr_INDUCT,ntp4vc_fra_expr_RECURSION =
  define_type
   "ntp4vc_fra_expr =
      NTP4VC_FRA_Evar ntp4vc_fra_addr
    | NTP4VC_FRA_Eneg ntp4vc_fra_expr
    | NTP4VC_FRA_Eadd ntp4vc_fra_expr ntp4vc_fra_expr";;

let ntp4vc_fra_instr_INDUCT,ntp4vc_fra_instr_RECURSION =
  define_type
   "ntp4vc_fra_instr =
      NTP4VC_FRA_Iload ntp4vc_fra_addr int
    | NTP4VC_FRA_Ineg int
    | NTP4VC_FRA_Iadd int int
    | NTP4VC_FRA_Ipush int
    | NTP4VC_FRA_Ipop int";;

let ntp4vc_fra_state_INDUCT,ntp4vc_fra_state_RECURSION =
  define_type
   "ntp4vc_fra_state =
      NTP4VC_FRA_State
        (ntp4vc_fra_addr->int) (int->int) (int list)";;

let ntp4vc_fra_mem =
  new_recursive_definition ntp4vc_fra_state_RECURSION
   `ntp4vc_fra_mem (NTP4VC_FRA_State mem reg st) = mem`;;

let ntp4vc_fra_reg =
  new_recursive_definition ntp4vc_fra_state_RECURSION
   `ntp4vc_fra_reg (NTP4VC_FRA_State mem reg st) = reg`;;

let ntp4vc_fra_stack =
  new_recursive_definition ntp4vc_fra_state_RECURSION
   `ntp4vc_fra_stack (NTP4VC_FRA_State mem reg st) = st`;;

let ntp4vc_fra_eval =
  new_recursive_definition ntp4vc_fra_expr_RECURSION
   `(!mem:ntp4vc_fra_addr->int.
     !x:ntp4vc_fra_addr.
       ntp4vc_fra_eval mem (NTP4VC_FRA_Evar x) = mem x) /\
    (!mem:ntp4vc_fra_addr->int.
     !e:ntp4vc_fra_expr.
       ntp4vc_fra_eval mem (NTP4VC_FRA_Eneg e) =
       --(ntp4vc_fra_eval mem e)) /\
    (!mem:ntp4vc_fra_addr->int.
     !e1 e2:ntp4vc_fra_expr.
       ntp4vc_fra_eval mem (NTP4VC_FRA_Eadd e1 e2) =
       ntp4vc_fra_eval mem e1 + ntp4vc_fra_eval mem e2)`;;

let ntp4vc_fra_update = new_definition
 `ntp4vc_fra_update (reg:int->int) (r:int) (v:int) =
    \r':int. if r' = r then v else reg r'`;;

let ntp4vc_fra_exec =
  new_recursive_definition ntp4vc_fra_instr_RECURSION
   `(!x:ntp4vc_fra_addr.
     !r:int.
     !s:ntp4vc_fra_state.
       ntp4vc_fra_exec (NTP4VC_FRA_Iload x r) s =
       NTP4VC_FRA_State
         (ntp4vc_fra_mem s)
         (ntp4vc_fra_update
           (ntp4vc_fra_reg s) r (ntp4vc_fra_mem s x))
         (ntp4vc_fra_stack s)) /\
    (!r:int.
     !s:ntp4vc_fra_state.
       ntp4vc_fra_exec (NTP4VC_FRA_Ineg r) s =
       NTP4VC_FRA_State
         (ntp4vc_fra_mem s)
         (ntp4vc_fra_update
           (ntp4vc_fra_reg s) r (--(ntp4vc_fra_reg s r)))
         (ntp4vc_fra_stack s)) /\
    (!r1 r2:int.
     !s:ntp4vc_fra_state.
       ntp4vc_fra_exec (NTP4VC_FRA_Iadd r1 r2) s =
       NTP4VC_FRA_State
         (ntp4vc_fra_mem s)
         (ntp4vc_fra_update
           (ntp4vc_fra_reg s) r2
           (ntp4vc_fra_reg s r1 + ntp4vc_fra_reg s r2))
         (ntp4vc_fra_stack s)) /\
    (!r:int.
     !s:ntp4vc_fra_state.
       ntp4vc_fra_exec (NTP4VC_FRA_Ipush r) s =
       NTP4VC_FRA_State
         (ntp4vc_fra_mem s)
         (ntp4vc_fra_reg s)
         (CONS (ntp4vc_fra_reg s r) (ntp4vc_fra_stack s))) /\
    (!r:int.
     !s:ntp4vc_fra_state.
       ntp4vc_fra_exec (NTP4VC_FRA_Ipop r) s =
       if ntp4vc_fra_stack s = [] then
         s
       else
         NTP4VC_FRA_State
           (ntp4vc_fra_mem s)
           (ntp4vc_fra_update
             (ntp4vc_fra_reg s) r (HD (ntp4vc_fra_stack s)))
           (TL (ntp4vc_fra_stack s)))`;;

let ntp4vc_fra_exec_list =
  new_recursive_definition list_RECURSION
   `(!s:ntp4vc_fra_state.
       ntp4vc_fra_exec_list ([]:ntp4vc_fra_instr list) s = s) /\
    (!i:ntp4vc_fra_instr.
     !code:ntp4vc_fra_instr list.
     !s:ntp4vc_fra_state.
       ntp4vc_fra_exec_list (CONS i code) s =
       ntp4vc_fra_exec_list code (ntp4vc_fra_exec i s))`;;

let ntp4vc_fra_expr_post = new_definition
 `ntp4vc_fra_expr_post
    (e:ntp4vc_fra_expr) (r:int)
    (s:ntp4vc_fra_state) (s':ntp4vc_fra_state) <=>
    ntp4vc_fra_mem s' = ntp4vc_fra_mem s /\
    ntp4vc_fra_reg s' r = ntp4vc_fra_eval (ntp4vc_fra_mem s) e /\
    ntp4vc_fra_stack s' = ntp4vc_fra_stack s /\
    (!r':int.
       r' < r ==> ntp4vc_fra_reg s' r' = ntp4vc_fra_reg s r')`;;

let ntp4vc_fra_hcode_INDUCT,ntp4vc_fra_hcode_RECURSION =
  define_type
   "ntp4vc_fra_hcode =
      NTP4VC_FRA_Hcode
        (ntp4vc_fra_instr list)
        (ntp4vc_fra_state->ntp4vc_fra_state->bool)";;

let ntp4vc_fra_wcode_INDUCT,ntp4vc_fra_wcode_RECURSION =
  define_type
   "ntp4vc_fra_wcode =
      NTP4VC_FRA_Wcode
        ((ntp4vc_fra_state->bool)->ntp4vc_fra_state->bool)
        (ntp4vc_fra_instr list)";;

let ntp4vc_fra_hpost =
  new_recursive_definition ntp4vc_fra_hcode_RECURSION
   `ntp4vc_fra_hpost (NTP4VC_FRA_Hcode code pst) = pst`;;

let ntp4vc_fra_hcode_body =
  new_recursive_definition ntp4vc_fra_hcode_RECURSION
   `ntp4vc_fra_hcode_body (NTP4VC_FRA_Hcode code pst) = code`;;

let ntp4vc_fra_wtrans =
  new_recursive_definition ntp4vc_fra_wcode_RECURSION
   `ntp4vc_fra_wtrans (NTP4VC_FRA_Wcode trans code) = trans`;;

let ntp4vc_fra_wcode_body =
  new_recursive_definition ntp4vc_fra_wcode_RECURSION
   `ntp4vc_fra_wcode_body (NTP4VC_FRA_Wcode trans code) = code`;;

let ntp4vc_fra_hcode_ok = new_definition
 `ntp4vc_fra_hcode_ok (hc:ntp4vc_fra_hcode) <=>
    !s:ntp4vc_fra_state.
      ntp4vc_fra_hpost hc s
        (ntp4vc_fra_exec_list (ntp4vc_fra_hcode_body hc) s)`;;

let ntp4vc_fra_wcode_ok = new_definition
 `ntp4vc_fra_wcode_ok (wc:ntp4vc_fra_wcode) <=>
    !q:ntp4vc_fra_state->bool.
    !s:ntp4vc_fra_state.
      ntp4vc_fra_wtrans wc q s
      ==> q (ntp4vc_fra_exec_list (ntp4vc_fra_wcode_body wc) s)`;;

let ntp4vc_fra_to_wp = new_definition
 `ntp4vc_fra_to_wp
    (pst:ntp4vc_fra_state->ntp4vc_fra_state->bool)
    (q:ntp4vc_fra_state->bool) (s1:ntp4vc_fra_state) <=>
    !s2:ntp4vc_fra_state. pst s1 s2 ==> q s2`;;

let ntp4vc_fra_rcompose = new_definition
 `ntp4vc_fra_rcompose (f:A->B) (g:B->C) (x:A) = g (f x)`;;

let ntp4vc_fra_identity = new_definition
 `ntp4vc_fra_identity (y:ntp4vc_fra_state->bool) = y`;;

let ntp4vc_fra_exec_closure = new_definition
 `ntp4vc_fra_exec_closure
    (i:ntp4vc_fra_instr) (s:ntp4vc_fra_state) =
    ntp4vc_fra_exec i s`;;

let ntp4vc_fra_direct_child =
  new_recursive_definition ntp4vc_fra_expr_RECURSION
   `(!x:ntp4vc_fra_addr.
     !child:ntp4vc_fra_expr.
       ntp4vc_fra_direct_child (NTP4VC_FRA_Evar x) child <=> F) /\
    (!e child:ntp4vc_fra_expr.
       ntp4vc_fra_direct_child (NTP4VC_FRA_Eneg e) child <=>
       e = child) /\
    (!e1 e2 child:ntp4vc_fra_expr.
       ntp4vc_fra_direct_child (NTP4VC_FRA_Eadd e1 e2) child <=>
       e1 = child \/ e2 = child)`;;

let ntp4vc_fra_compile_pre_add = new_definition
 `ntp4vc_fra_compile_pre_add
    (k:int) (r:int) (e1:ntp4vc_fra_expr) (e2:ntp4vc_fra_expr) <=>
    COND (r < k - (&1:int))
         (!o2:ntp4vc_fra_wcode.
           ntp4vc_fra_wcode_ok o2 /\
           ntp4vc_fra_wtrans o2 = ntp4vc_fra_identity
           ==>
           ntp4vc_fra_wcode_ok o2 /\
           (!o3:ntp4vc_fra_wcode.
              ntp4vc_fra_wcode_ok o3 /\
              ntp4vc_fra_wtrans o3 =
                ntp4vc_fra_rcompose
                  (ntp4vc_fra_wtrans o2)
                  (ntp4vc_fra_rcompose
                    (ntp4vc_fra_exec_closure
                      (NTP4VC_FRA_Iadd (r + (&1:int)) r)))
              ==>
              let o4 = r + (&1:int) in
              (ntp4vc_fra_direct_child
                 (NTP4VC_FRA_Eadd e1 e2) e2 /\
               (&0:int) <= o4 /\ o4 < k) /\
              (!o5:ntp4vc_fra_hcode.
                 ntp4vc_fra_hcode_ok o5 /\
                 ntp4vc_fra_hpost o5 = ntp4vc_fra_expr_post e2 o4
                 ==>
                 ntp4vc_fra_hcode_ok o5 /\
                 (!o6:ntp4vc_fra_wcode.
                    ntp4vc_fra_wcode_ok o6 /\
                    ntp4vc_fra_wtrans o6 =
                      ntp4vc_fra_to_wp (ntp4vc_fra_hpost o5)
                    ==>
                    (ntp4vc_fra_direct_child
                       (NTP4VC_FRA_Eadd e1 e2) e1 /\
                     (&0:int) <= r /\ r < k) /\
                    (!o7:ntp4vc_fra_hcode.
                       ntp4vc_fra_hcode_ok o7 /\
                       ntp4vc_fra_hpost o7 =
                         ntp4vc_fra_expr_post e1 r
                       ==>
                       ntp4vc_fra_hcode_ok o7 /\
                       (!o8:ntp4vc_fra_wcode.
                          ntp4vc_fra_wcode_ok o8 /\
                          ntp4vc_fra_wtrans o8 =
                            ntp4vc_fra_to_wp
                              (ntp4vc_fra_hpost o7)
                          ==>
                          (ntp4vc_fra_wcode_ok o8 /\
                           ntp4vc_fra_wcode_ok o6) /\
                          (!o9:ntp4vc_fra_wcode.
                             ntp4vc_fra_wcode_ok o9 /\
                             ntp4vc_fra_wtrans o9 =
                               ntp4vc_fra_rcompose
                                 (ntp4vc_fra_wtrans o6)
                                 (ntp4vc_fra_wtrans o8)
                             ==>
                             ntp4vc_fra_wcode_ok o9 /\
                             ntp4vc_fra_wcode_ok o3)))))))
         (!o2:ntp4vc_fra_wcode.
           ntp4vc_fra_wcode_ok o2 /\
           ntp4vc_fra_wtrans o2 = ntp4vc_fra_identity
           ==>
           ntp4vc_fra_wcode_ok o2 /\
           (!o3:ntp4vc_fra_wcode.
              ntp4vc_fra_wcode_ok o3 /\
              ntp4vc_fra_wtrans o3 =
                ntp4vc_fra_rcompose
                  (ntp4vc_fra_wtrans o2)
                  (ntp4vc_fra_rcompose
                    (ntp4vc_fra_exec_closure
                      (NTP4VC_FRA_Ipop (k - (&2:int)))))
              ==>
              ntp4vc_fra_wcode_ok o3 /\
              (!o4:ntp4vc_fra_wcode.
                 ntp4vc_fra_wcode_ok o4 /\
                 ntp4vc_fra_wtrans o4 =
                   ntp4vc_fra_rcompose
                     (ntp4vc_fra_wtrans o3)
                     (ntp4vc_fra_rcompose
                       (ntp4vc_fra_exec_closure
                         (NTP4VC_FRA_Iadd
                           (k - (&2:int)) (k - (&1:int)))))
                 ==>
                 let o5 = k - (&1:int) in
                 (ntp4vc_fra_direct_child
                    (NTP4VC_FRA_Eadd e1 e2) e2 /\
                  (&0:int) <= o5 /\ o5 < k) /\
                 (!o6:ntp4vc_fra_hcode.
                    ntp4vc_fra_hcode_ok o6 /\
                    ntp4vc_fra_hpost o6 =
                      ntp4vc_fra_expr_post e2 o5
                    ==>
                    ntp4vc_fra_hcode_ok o6 /\
                    (!o7:ntp4vc_fra_wcode.
                       ntp4vc_fra_wcode_ok o7 /\
                       ntp4vc_fra_wtrans o7 =
                         ntp4vc_fra_to_wp (ntp4vc_fra_hpost o6)
                       ==>
                       let o8 = k - (&2:int) in
                       (ntp4vc_fra_direct_child
                          (NTP4VC_FRA_Eadd e1 e2) e1 /\
                        (&0:int) <= o8 /\ o8 < k) /\
                       (!o9:ntp4vc_fra_hcode.
                          ntp4vc_fra_hcode_ok o9 /\
                          ntp4vc_fra_hpost o9 =
                            ntp4vc_fra_expr_post e1 o8
                          ==>
                          ntp4vc_fra_hcode_ok o9 /\
                          (!o10:ntp4vc_fra_wcode.
                             ntp4vc_fra_wcode_ok o10 /\
                             ntp4vc_fra_wtrans o10 =
                               ntp4vc_fra_to_wp
                                 (ntp4vc_fra_hpost o9)
                             ==>
                             (ntp4vc_fra_wcode_ok o10 /\
                              ntp4vc_fra_wcode_ok o7) /\
                             (!o11:ntp4vc_fra_wcode.
                                ntp4vc_fra_wcode_ok o11 /\
                                ntp4vc_fra_wtrans o11 =
                                  ntp4vc_fra_rcompose
                                    (ntp4vc_fra_wtrans o7)
                                    (ntp4vc_fra_wtrans o10)
                                ==>
                                (ntp4vc_fra_wcode_ok o11 /\
                                 ntp4vc_fra_wcode_ok o4) /\
                                (!o12:ntp4vc_fra_wcode.
                                   ntp4vc_fra_wcode_ok o12 /\
                                   ntp4vc_fra_wtrans o12 =
                                     ntp4vc_fra_rcompose
                                       (ntp4vc_fra_wtrans o4)
                                       (ntp4vc_fra_wtrans o11)
                                   ==>
                                   ntp4vc_fra_wcode_ok o12)))))))))`;;

let ntp4vc_fra_compile_pre =
  new_recursive_definition ntp4vc_fra_expr_RECURSION
   `(!k r:int.
     !x:ntp4vc_fra_addr.
       ntp4vc_fra_compile_pre k r (NTP4VC_FRA_Evar x) <=>
       (!o2:ntp4vc_fra_wcode.
          ntp4vc_fra_wcode_ok o2 /\
          ntp4vc_fra_wtrans o2 = ntp4vc_fra_identity
          ==> ntp4vc_fra_wcode_ok o2)) /\
    (!k r:int.
     !e1:ntp4vc_fra_expr.
       ntp4vc_fra_compile_pre k r (NTP4VC_FRA_Eneg e1) <=>
       (!o2:ntp4vc_fra_wcode.
          ntp4vc_fra_wcode_ok o2 /\
          ntp4vc_fra_wtrans o2 = ntp4vc_fra_identity
          ==>
          ntp4vc_fra_wcode_ok o2 /\
          (!o3:ntp4vc_fra_wcode.
             ntp4vc_fra_wcode_ok o3 /\
             ntp4vc_fra_wtrans o3 =
               ntp4vc_fra_rcompose
                 (ntp4vc_fra_wtrans o2)
                 (ntp4vc_fra_rcompose
                   (ntp4vc_fra_exec_closure
                     (NTP4VC_FRA_Ineg r)))
             ==>
             (ntp4vc_fra_direct_child
                (NTP4VC_FRA_Eneg e1) e1 /\
              (&0:int) <= r /\ r < k) /\
             (!o4:ntp4vc_fra_hcode.
                ntp4vc_fra_hcode_ok o4 /\
                ntp4vc_fra_hpost o4 = ntp4vc_fra_expr_post e1 r
                ==>
                ntp4vc_fra_hcode_ok o4 /\
                (!o5:ntp4vc_fra_wcode.
                   ntp4vc_fra_wcode_ok o5 /\
                   ntp4vc_fra_wtrans o5 =
                     ntp4vc_fra_to_wp (ntp4vc_fra_hpost o4)
                   ==>
                   ntp4vc_fra_wcode_ok o5 /\
                   ntp4vc_fra_wcode_ok o3))))) /\
    (!k r:int.
     !e1 e2:ntp4vc_fra_expr.
       ntp4vc_fra_compile_pre k r (NTP4VC_FRA_Eadd e1 e2) <=>
       ntp4vc_fra_compile_pre_add k r e1 e2)`;;

let ntp4vc_fra_compile_build_add = new_definition
 `ntp4vc_fra_compile_build_add
    (k:int) (r:int) (e1:ntp4vc_fra_expr) (e2:ntp4vc_fra_expr)
    (o2:ntp4vc_fra_wcode) <=>
    COND (r < k - (&1:int))
         (?o3:ntp4vc_fra_wcode.
           (ntp4vc_fra_wcode_ok o3 /\
            ntp4vc_fra_wtrans o3 = ntp4vc_fra_identity) /\
           (?o4:ntp4vc_fra_wcode.
              (ntp4vc_fra_wcode_ok o4 /\
               ntp4vc_fra_wtrans o4 =
                 ntp4vc_fra_rcompose
                   (ntp4vc_fra_wtrans o3)
                   (ntp4vc_fra_rcompose
                     (ntp4vc_fra_exec_closure
                       (NTP4VC_FRA_Iadd (r + (&1:int)) r)))) /\
              (?o5:ntp4vc_fra_hcode.
                 (ntp4vc_fra_hcode_ok o5 /\
                  ntp4vc_fra_hpost o5 =
                    ntp4vc_fra_expr_post e2 (r + (&1:int))) /\
                 (?o6:ntp4vc_fra_wcode.
                    (ntp4vc_fra_wcode_ok o6 /\
                     ntp4vc_fra_wtrans o6 =
                       ntp4vc_fra_to_wp (ntp4vc_fra_hpost o5)) /\
                    (?o7:ntp4vc_fra_hcode.
                       (ntp4vc_fra_hcode_ok o7 /\
                        ntp4vc_fra_hpost o7 =
                          ntp4vc_fra_expr_post e1 r) /\
                       (?o8:ntp4vc_fra_wcode.
                          (ntp4vc_fra_wcode_ok o8 /\
                           ntp4vc_fra_wtrans o8 =
                             ntp4vc_fra_to_wp
                               (ntp4vc_fra_hpost o7)) /\
                          (?o9:ntp4vc_fra_wcode.
                             (ntp4vc_fra_wcode_ok o9 /\
                              ntp4vc_fra_wtrans o9 =
                                ntp4vc_fra_rcompose
                                  (ntp4vc_fra_wtrans o6)
                                  (ntp4vc_fra_wtrans o8)) /\
                             ntp4vc_fra_wcode_ok o2 /\
                             ntp4vc_fra_wtrans o2 =
                               ntp4vc_fra_rcompose
                                 (ntp4vc_fra_wtrans o4)
                                 (ntp4vc_fra_wtrans o9))))))))
         (?o3:ntp4vc_fra_wcode.
           (ntp4vc_fra_wcode_ok o3 /\
            ntp4vc_fra_wtrans o3 = ntp4vc_fra_identity) /\
           (?o4:ntp4vc_fra_wcode.
              (ntp4vc_fra_wcode_ok o4 /\
               ntp4vc_fra_wtrans o4 =
                 ntp4vc_fra_rcompose
                   (ntp4vc_fra_wtrans o3)
                   (ntp4vc_fra_rcompose
                     (ntp4vc_fra_exec_closure
                       (NTP4VC_FRA_Ipop (k - (&2:int)))))) /\
              (?o5:ntp4vc_fra_wcode.
                 (ntp4vc_fra_wcode_ok o5 /\
                  ntp4vc_fra_wtrans o5 =
                    ntp4vc_fra_rcompose
                      (ntp4vc_fra_wtrans o4)
                      (ntp4vc_fra_rcompose
                        (ntp4vc_fra_exec_closure
                          (NTP4VC_FRA_Iadd
                            (k - (&2:int)) (k - (&1:int)))))) /\
                 (?o6:ntp4vc_fra_hcode.
                    (ntp4vc_fra_hcode_ok o6 /\
                     ntp4vc_fra_hpost o6 =
                       ntp4vc_fra_expr_post e2 (k - (&1:int))) /\
                    (?o7:ntp4vc_fra_wcode.
                       (ntp4vc_fra_wcode_ok o7 /\
                        ntp4vc_fra_wtrans o7 =
                          ntp4vc_fra_to_wp (ntp4vc_fra_hpost o6)) /\
                       (?o8:ntp4vc_fra_hcode.
                          (ntp4vc_fra_hcode_ok o8 /\
                           ntp4vc_fra_hpost o8 =
                             ntp4vc_fra_expr_post
                               e1 (k - (&2:int))) /\
                          (?o9:ntp4vc_fra_wcode.
                             (ntp4vc_fra_wcode_ok o9 /\
                              ntp4vc_fra_wtrans o9 =
                                ntp4vc_fra_to_wp
                                  (ntp4vc_fra_hpost o8)) /\
                             (?o10:ntp4vc_fra_wcode.
                                (ntp4vc_fra_wcode_ok o10 /\
                                 ntp4vc_fra_wtrans o10 =
                                   ntp4vc_fra_rcompose
                                     (ntp4vc_fra_wtrans o7)
                                     (ntp4vc_fra_wtrans o9)) /\
                                (?o11:ntp4vc_fra_wcode.
                                   (ntp4vc_fra_wcode_ok o11 /\
                                    ntp4vc_fra_wtrans o11 =
                                      ntp4vc_fra_rcompose
                                        (ntp4vc_fra_wtrans o5)
                                        (ntp4vc_fra_wtrans o10)) /\
                                   ntp4vc_fra_wcode_ok o2 /\
                                   ntp4vc_fra_wtrans o2 =
                                     ntp4vc_fra_rcompose
                                       (ntp4vc_fra_wtrans o11)
                                       (ntp4vc_fra_rcompose
                                         (ntp4vc_fra_exec_closure
                                           (NTP4VC_FRA_Ipush
                                             (k - (&2:int))))))))))))))`;;

let ntp4vc_fra_compile_build =
  new_recursive_definition ntp4vc_fra_expr_RECURSION
   `(!k r:int.
     !x:ntp4vc_fra_addr.
     !o2:ntp4vc_fra_wcode.
       ntp4vc_fra_compile_build k r (NTP4VC_FRA_Evar x) o2 <=>
       ?o3:ntp4vc_fra_wcode.
         (ntp4vc_fra_wcode_ok o3 /\
          ntp4vc_fra_wtrans o3 = ntp4vc_fra_identity) /\
         ntp4vc_fra_wcode_ok o2 /\
         ntp4vc_fra_wtrans o2 =
           ntp4vc_fra_rcompose
             (ntp4vc_fra_wtrans o3)
             (ntp4vc_fra_rcompose
               (ntp4vc_fra_exec_closure
                 (NTP4VC_FRA_Iload x r)))) /\
    (!k r:int.
     !e1:ntp4vc_fra_expr.
     !o2:ntp4vc_fra_wcode.
       ntp4vc_fra_compile_build k r (NTP4VC_FRA_Eneg e1) o2 <=>
       ?o3:ntp4vc_fra_wcode.
         (ntp4vc_fra_wcode_ok o3 /\
          ntp4vc_fra_wtrans o3 = ntp4vc_fra_identity) /\
         (?o4:ntp4vc_fra_wcode.
            (ntp4vc_fra_wcode_ok o4 /\
             ntp4vc_fra_wtrans o4 =
               ntp4vc_fra_rcompose
                 (ntp4vc_fra_wtrans o3)
                 (ntp4vc_fra_rcompose
                   (ntp4vc_fra_exec_closure
                     (NTP4VC_FRA_Ineg r)))) /\
            (?o5:ntp4vc_fra_hcode.
               (ntp4vc_fra_hcode_ok o5 /\
                ntp4vc_fra_hpost o5 = ntp4vc_fra_expr_post e1 r) /\
               (?o6:ntp4vc_fra_wcode.
                  (ntp4vc_fra_wcode_ok o6 /\
                   ntp4vc_fra_wtrans o6 =
                     ntp4vc_fra_to_wp (ntp4vc_fra_hpost o5)) /\
                  ntp4vc_fra_wcode_ok o2 /\
                  ntp4vc_fra_wtrans o2 =
                    ntp4vc_fra_rcompose
                      (ntp4vc_fra_wtrans o4)
                      (ntp4vc_fra_wtrans o6))))) /\
    (!k r:int.
     !e1 e2:ntp4vc_fra_expr.
     !o2:ntp4vc_fra_wcode.
       ntp4vc_fra_compile_build k r (NTP4VC_FRA_Eadd e1 e2) o2 <=>
       ntp4vc_fra_compile_build_add k r e1 e2 o2)`;;

let statement =
 `!k:int.
    (&2:int) <= k
    ==>
    !r:int.
    !e:ntp4vc_fra_expr.
      (&0:int) <= r
      ==>
      r < k
      ==>
      ntp4vc_fra_compile_pre k r e /\
      (!o2:ntp4vc_fra_wcode.
         ntp4vc_fra_compile_build k r e o2
         ==>
         (ntp4vc_fra_wcode_ok o2 /\
          (!x:ntp4vc_fra_state.
             ntp4vc_fra_wtrans o2
               (ntp4vc_fra_expr_post e r x) x)) /\
         (!result:ntp4vc_fra_hcode.
            ntp4vc_fra_hcode_ok result /\
            ntp4vc_fra_hpost result = ntp4vc_fra_expr_post e r
            ==>
            ntp4vc_fra_hcode_ok result /\
            ntp4vc_fra_hpost result = ntp4vc_fra_expr_post e r))`;;
