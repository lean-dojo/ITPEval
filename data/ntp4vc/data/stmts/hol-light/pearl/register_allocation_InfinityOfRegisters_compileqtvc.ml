(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/register_allocation_InfinityOfRegisters_compileqtvc: the
  unbounded-register expression compiler verification condition, including
  recursive register allocation and double-WP correctness. This file contains
  no proof.
*)

new_type ("ntp4vc_ira_addr",0);;

let ntp4vc_ira_expr_INDUCT,ntp4vc_ira_expr_RECURSION =
  define_type
   "ntp4vc_ira_expr =
      NTP4VC_IRA_Evar ntp4vc_ira_addr
    | NTP4VC_IRA_Eneg ntp4vc_ira_expr
    | NTP4VC_IRA_Eadd ntp4vc_ira_expr ntp4vc_ira_expr";;

let ntp4vc_ira_instr_INDUCT,ntp4vc_ira_instr_RECURSION =
  define_type
   "ntp4vc_ira_instr =
      NTP4VC_IRA_Iload ntp4vc_ira_addr int
    | NTP4VC_IRA_Ineg int
    | NTP4VC_IRA_Iadd int int
    | NTP4VC_IRA_Ipush int
    | NTP4VC_IRA_Ipop int";;

let ntp4vc_ira_state_INDUCT,ntp4vc_ira_state_RECURSION =
  define_type
   "ntp4vc_ira_state =
      NTP4VC_IRA_State
        (ntp4vc_ira_addr->int) (int->int) (int list)";;

let ntp4vc_ira_mem =
  new_recursive_definition ntp4vc_ira_state_RECURSION
   `ntp4vc_ira_mem (NTP4VC_IRA_State mem reg st) = mem`;;

let ntp4vc_ira_reg =
  new_recursive_definition ntp4vc_ira_state_RECURSION
   `ntp4vc_ira_reg (NTP4VC_IRA_State mem reg st) = reg`;;

let ntp4vc_ira_stack =
  new_recursive_definition ntp4vc_ira_state_RECURSION
   `ntp4vc_ira_stack (NTP4VC_IRA_State mem reg st) = st`;;

let ntp4vc_ira_eval =
  new_recursive_definition ntp4vc_ira_expr_RECURSION
   `(!mem:ntp4vc_ira_addr->int.
     !x:ntp4vc_ira_addr.
       ntp4vc_ira_eval mem (NTP4VC_IRA_Evar x) = mem x) /\
    (!mem:ntp4vc_ira_addr->int.
     !e:ntp4vc_ira_expr.
       ntp4vc_ira_eval mem (NTP4VC_IRA_Eneg e) =
       --(ntp4vc_ira_eval mem e)) /\
    (!mem:ntp4vc_ira_addr->int.
     !e1 e2:ntp4vc_ira_expr.
       ntp4vc_ira_eval mem (NTP4VC_IRA_Eadd e1 e2) =
       ntp4vc_ira_eval mem e1 + ntp4vc_ira_eval mem e2)`;;

let ntp4vc_ira_update = new_definition
 `ntp4vc_ira_update (reg:int->int) (r:int) (v:int) =
    \r':int. if r' = r then v else reg r'`;;

let ntp4vc_ira_exec =
  new_recursive_definition ntp4vc_ira_instr_RECURSION
   `(!x:ntp4vc_ira_addr.
     !r:int.
     !s:ntp4vc_ira_state.
       ntp4vc_ira_exec (NTP4VC_IRA_Iload x r) s =
       NTP4VC_IRA_State
         (ntp4vc_ira_mem s)
         (ntp4vc_ira_update
           (ntp4vc_ira_reg s) r (ntp4vc_ira_mem s x))
         (ntp4vc_ira_stack s)) /\
    (!r:int.
     !s:ntp4vc_ira_state.
       ntp4vc_ira_exec (NTP4VC_IRA_Ineg r) s =
       NTP4VC_IRA_State
         (ntp4vc_ira_mem s)
         (ntp4vc_ira_update
           (ntp4vc_ira_reg s) r (--(ntp4vc_ira_reg s r)))
         (ntp4vc_ira_stack s)) /\
    (!r1 r2:int.
     !s:ntp4vc_ira_state.
       ntp4vc_ira_exec (NTP4VC_IRA_Iadd r1 r2) s =
       NTP4VC_IRA_State
         (ntp4vc_ira_mem s)
         (ntp4vc_ira_update
           (ntp4vc_ira_reg s) r2
           (ntp4vc_ira_reg s r1 + ntp4vc_ira_reg s r2))
         (ntp4vc_ira_stack s)) /\
    (!r:int.
     !s:ntp4vc_ira_state.
       ntp4vc_ira_exec (NTP4VC_IRA_Ipush r) s =
       NTP4VC_IRA_State
         (ntp4vc_ira_mem s)
         (ntp4vc_ira_reg s)
         (CONS (ntp4vc_ira_reg s r) (ntp4vc_ira_stack s))) /\
    (!r:int.
     !s:ntp4vc_ira_state.
       ntp4vc_ira_exec (NTP4VC_IRA_Ipop r) s =
       if ntp4vc_ira_stack s = [] then
         s
       else
         NTP4VC_IRA_State
           (ntp4vc_ira_mem s)
           (ntp4vc_ira_update
             (ntp4vc_ira_reg s) r (HD (ntp4vc_ira_stack s)))
           (TL (ntp4vc_ira_stack s)))`;;

let ntp4vc_ira_exec_list =
  new_recursive_definition list_RECURSION
   `(!s:ntp4vc_ira_state.
       ntp4vc_ira_exec_list ([]:ntp4vc_ira_instr list) s = s) /\
    (!i:ntp4vc_ira_instr.
     !code:ntp4vc_ira_instr list.
     !s:ntp4vc_ira_state.
       ntp4vc_ira_exec_list (CONS i code) s =
       ntp4vc_ira_exec_list code (ntp4vc_ira_exec i s))`;;

let ntp4vc_ira_expr_post = new_definition
 `ntp4vc_ira_expr_post
    (e:ntp4vc_ira_expr) (r:int)
    (s:ntp4vc_ira_state) (s':ntp4vc_ira_state) <=>
    ntp4vc_ira_mem s' = ntp4vc_ira_mem s /\
    ntp4vc_ira_reg s' r = ntp4vc_ira_eval (ntp4vc_ira_mem s) e /\
    ntp4vc_ira_stack s' = ntp4vc_ira_stack s /\
    (!r':int.
       r' < r ==> ntp4vc_ira_reg s' r' = ntp4vc_ira_reg s r')`;;

let ntp4vc_ira_hcode_INDUCT,ntp4vc_ira_hcode_RECURSION =
  define_type
   "ntp4vc_ira_hcode =
      NTP4VC_IRA_Hcode
        (ntp4vc_ira_instr list)
        (ntp4vc_ira_state->ntp4vc_ira_state->bool)";;

let ntp4vc_ira_wcode_INDUCT,ntp4vc_ira_wcode_RECURSION =
  define_type
   "ntp4vc_ira_wcode =
      NTP4VC_IRA_Wcode
        ((ntp4vc_ira_state->bool)->ntp4vc_ira_state->bool)
        (ntp4vc_ira_instr list)";;

let ntp4vc_ira_hpost =
  new_recursive_definition ntp4vc_ira_hcode_RECURSION
   `ntp4vc_ira_hpost (NTP4VC_IRA_Hcode code pst) = pst`;;

let ntp4vc_ira_hcode_body =
  new_recursive_definition ntp4vc_ira_hcode_RECURSION
   `ntp4vc_ira_hcode_body (NTP4VC_IRA_Hcode code pst) = code`;;

let ntp4vc_ira_wtrans =
  new_recursive_definition ntp4vc_ira_wcode_RECURSION
   `ntp4vc_ira_wtrans (NTP4VC_IRA_Wcode trans code) = trans`;;

let ntp4vc_ira_wcode_body =
  new_recursive_definition ntp4vc_ira_wcode_RECURSION
   `ntp4vc_ira_wcode_body (NTP4VC_IRA_Wcode trans code) = code`;;

let ntp4vc_ira_hcode_ok = new_definition
 `ntp4vc_ira_hcode_ok (hc:ntp4vc_ira_hcode) <=>
    !s:ntp4vc_ira_state.
      ntp4vc_ira_hpost hc s
        (ntp4vc_ira_exec_list (ntp4vc_ira_hcode_body hc) s)`;;

let ntp4vc_ira_wcode_ok = new_definition
 `ntp4vc_ira_wcode_ok (wc:ntp4vc_ira_wcode) <=>
    !q:ntp4vc_ira_state->bool.
    !s:ntp4vc_ira_state.
      ntp4vc_ira_wtrans wc q s
      ==> q (ntp4vc_ira_exec_list (ntp4vc_ira_wcode_body wc) s)`;;

let ntp4vc_ira_to_wp = new_definition
 `ntp4vc_ira_to_wp
    (pst:ntp4vc_ira_state->ntp4vc_ira_state->bool)
    (q:ntp4vc_ira_state->bool) (s1:ntp4vc_ira_state) <=>
    !s2:ntp4vc_ira_state. pst s1 s2 ==> q s2`;;

let ntp4vc_ira_rcompose = new_definition
 `ntp4vc_ira_rcompose (f:A->B) (g:B->C) (x:A) = g (f x)`;;

let ntp4vc_ira_identity = new_definition
 `ntp4vc_ira_identity (y:ntp4vc_ira_state->bool) = y`;;

let ntp4vc_ira_exec_closure = new_definition
 `ntp4vc_ira_exec_closure
    (i:ntp4vc_ira_instr) (s:ntp4vc_ira_state) =
    ntp4vc_ira_exec i s`;;

let ntp4vc_ira_direct_child =
  new_recursive_definition ntp4vc_ira_expr_RECURSION
   `(!x:ntp4vc_ira_addr.
     !child:ntp4vc_ira_expr.
       ntp4vc_ira_direct_child (NTP4VC_IRA_Evar x) child <=> F) /\
    (!e child:ntp4vc_ira_expr.
       ntp4vc_ira_direct_child (NTP4VC_IRA_Eneg e) child <=>
       e = child) /\
    (!e1 e2 child:ntp4vc_ira_expr.
       ntp4vc_ira_direct_child (NTP4VC_IRA_Eadd e1 e2) child <=>
       e1 = child \/ e2 = child)`;;

let ntp4vc_ira_compile_pre =
  new_recursive_definition ntp4vc_ira_expr_RECURSION
   `(!r:int.
     !x:ntp4vc_ira_addr.
       ntp4vc_ira_compile_pre r (NTP4VC_IRA_Evar x) <=>
       (!o2:ntp4vc_ira_wcode.
          ntp4vc_ira_wcode_ok o2 /\
          ntp4vc_ira_wtrans o2 = ntp4vc_ira_identity
          ==> ntp4vc_ira_wcode_ok o2)) /\
    (!r:int.
     !e1:ntp4vc_ira_expr.
       ntp4vc_ira_compile_pre r (NTP4VC_IRA_Eneg e1) <=>
       (!o2:ntp4vc_ira_wcode.
          ntp4vc_ira_wcode_ok o2 /\
          ntp4vc_ira_wtrans o2 = ntp4vc_ira_identity
          ==>
          ntp4vc_ira_wcode_ok o2 /\
          (!o3:ntp4vc_ira_wcode.
             ntp4vc_ira_wcode_ok o3 /\
             ntp4vc_ira_wtrans o3 =
               ntp4vc_ira_rcompose
                 (ntp4vc_ira_wtrans o2)
                 (ntp4vc_ira_rcompose
                   (ntp4vc_ira_exec_closure
                     (NTP4VC_IRA_Ineg r)))
             ==>
             ntp4vc_ira_direct_child
               (NTP4VC_IRA_Eneg e1) e1 /\
             (!o4:ntp4vc_ira_hcode.
                ntp4vc_ira_hcode_ok o4 /\
                ntp4vc_ira_hpost o4 = ntp4vc_ira_expr_post e1 r
                ==>
                ntp4vc_ira_hcode_ok o4 /\
                (!o5:ntp4vc_ira_wcode.
                   ntp4vc_ira_wcode_ok o5 /\
                   ntp4vc_ira_wtrans o5 =
                     ntp4vc_ira_to_wp (ntp4vc_ira_hpost o4)
                   ==>
                   ntp4vc_ira_wcode_ok o5 /\
                   ntp4vc_ira_wcode_ok o3))))) /\
    (!r:int.
     !e1 e2:ntp4vc_ira_expr.
       ntp4vc_ira_compile_pre r (NTP4VC_IRA_Eadd e1 e2) <=>
       (!o2:ntp4vc_ira_wcode.
          ntp4vc_ira_wcode_ok o2 /\
          ntp4vc_ira_wtrans o2 = ntp4vc_ira_identity
          ==>
          ntp4vc_ira_wcode_ok o2 /\
          (!o3:ntp4vc_ira_wcode.
             ntp4vc_ira_wcode_ok o3 /\
             ntp4vc_ira_wtrans o3 =
               ntp4vc_ira_rcompose
                 (ntp4vc_ira_wtrans o2)
                 (ntp4vc_ira_rcompose
                   (ntp4vc_ira_exec_closure
                     (NTP4VC_IRA_Iadd (r + (&1:int)) r)))
             ==>
             ntp4vc_ira_direct_child
               (NTP4VC_IRA_Eadd e1 e2) e2 /\
             (!o4:ntp4vc_ira_hcode.
                ntp4vc_ira_hcode_ok o4 /\
                ntp4vc_ira_hpost o4 =
                  ntp4vc_ira_expr_post e2 (r + (&1:int))
                ==>
                ntp4vc_ira_hcode_ok o4 /\
                (!o5:ntp4vc_ira_wcode.
                   ntp4vc_ira_wcode_ok o5 /\
                   ntp4vc_ira_wtrans o5 =
                     ntp4vc_ira_to_wp (ntp4vc_ira_hpost o4)
                   ==>
                   ntp4vc_ira_direct_child
                     (NTP4VC_IRA_Eadd e1 e2) e1 /\
                   (!o6:ntp4vc_ira_hcode.
                      ntp4vc_ira_hcode_ok o6 /\
                      ntp4vc_ira_hpost o6 =
                        ntp4vc_ira_expr_post e1 r
                      ==>
                      ntp4vc_ira_hcode_ok o6 /\
                      (!o7:ntp4vc_ira_wcode.
                         ntp4vc_ira_wcode_ok o7 /\
                         ntp4vc_ira_wtrans o7 =
                           ntp4vc_ira_to_wp
                             (ntp4vc_ira_hpost o6)
                         ==>
                         (ntp4vc_ira_wcode_ok o7 /\
                          ntp4vc_ira_wcode_ok o5) /\
                         (!o8:ntp4vc_ira_wcode.
                            ntp4vc_ira_wcode_ok o8 /\
                            ntp4vc_ira_wtrans o8 =
                              ntp4vc_ira_rcompose
                                (ntp4vc_ira_wtrans o5)
                                (ntp4vc_ira_wtrans o7)
                            ==>
                            ntp4vc_ira_wcode_ok o8 /\
                            ntp4vc_ira_wcode_ok o3))))))))`;;

let ntp4vc_ira_compile_build =
  new_recursive_definition ntp4vc_ira_expr_RECURSION
   `(!r:int.
     !x:ntp4vc_ira_addr.
     !o2:ntp4vc_ira_wcode.
       ntp4vc_ira_compile_build r (NTP4VC_IRA_Evar x) o2 <=>
       ?o3:ntp4vc_ira_wcode.
         (ntp4vc_ira_wcode_ok o3 /\
          ntp4vc_ira_wtrans o3 = ntp4vc_ira_identity) /\
         ntp4vc_ira_wcode_ok o2 /\
         ntp4vc_ira_wtrans o2 =
           ntp4vc_ira_rcompose
             (ntp4vc_ira_wtrans o3)
             (ntp4vc_ira_rcompose
               (ntp4vc_ira_exec_closure
                 (NTP4VC_IRA_Iload x r)))) /\
    (!r:int.
     !e1:ntp4vc_ira_expr.
     !o2:ntp4vc_ira_wcode.
       ntp4vc_ira_compile_build r (NTP4VC_IRA_Eneg e1) o2 <=>
       ?o3:ntp4vc_ira_wcode.
         (ntp4vc_ira_wcode_ok o3 /\
          ntp4vc_ira_wtrans o3 = ntp4vc_ira_identity) /\
         (?o4:ntp4vc_ira_wcode.
            (ntp4vc_ira_wcode_ok o4 /\
             ntp4vc_ira_wtrans o4 =
               ntp4vc_ira_rcompose
                 (ntp4vc_ira_wtrans o3)
                 (ntp4vc_ira_rcompose
                   (ntp4vc_ira_exec_closure
                     (NTP4VC_IRA_Ineg r)))) /\
            (?o5:ntp4vc_ira_hcode.
               (ntp4vc_ira_hcode_ok o5 /\
                ntp4vc_ira_hpost o5 = ntp4vc_ira_expr_post e1 r) /\
               (?o6:ntp4vc_ira_wcode.
                  (ntp4vc_ira_wcode_ok o6 /\
                   ntp4vc_ira_wtrans o6 =
                     ntp4vc_ira_to_wp (ntp4vc_ira_hpost o5)) /\
                  ntp4vc_ira_wcode_ok o2 /\
                  ntp4vc_ira_wtrans o2 =
                    ntp4vc_ira_rcompose
                      (ntp4vc_ira_wtrans o4)
                      (ntp4vc_ira_wtrans o6))))) /\
    (!r:int.
     !e1 e2:ntp4vc_ira_expr.
     !o2:ntp4vc_ira_wcode.
       ntp4vc_ira_compile_build r (NTP4VC_IRA_Eadd e1 e2) o2 <=>
       ?o3:ntp4vc_ira_wcode.
         (ntp4vc_ira_wcode_ok o3 /\
          ntp4vc_ira_wtrans o3 = ntp4vc_ira_identity) /\
         (?o4:ntp4vc_ira_wcode.
            (ntp4vc_ira_wcode_ok o4 /\
             ntp4vc_ira_wtrans o4 =
               ntp4vc_ira_rcompose
                 (ntp4vc_ira_wtrans o3)
                 (ntp4vc_ira_rcompose
                   (ntp4vc_ira_exec_closure
                     (NTP4VC_IRA_Iadd (r + (&1:int)) r)))) /\
            (?o5:ntp4vc_ira_hcode.
               (ntp4vc_ira_hcode_ok o5 /\
                ntp4vc_ira_hpost o5 =
                  ntp4vc_ira_expr_post e2 (r + (&1:int))) /\
               (?o6:ntp4vc_ira_wcode.
                  (ntp4vc_ira_wcode_ok o6 /\
                   ntp4vc_ira_wtrans o6 =
                     ntp4vc_ira_to_wp (ntp4vc_ira_hpost o5)) /\
                  (?o7:ntp4vc_ira_hcode.
                     (ntp4vc_ira_hcode_ok o7 /\
                      ntp4vc_ira_hpost o7 =
                        ntp4vc_ira_expr_post e1 r) /\
                     (?o8:ntp4vc_ira_wcode.
                        (ntp4vc_ira_wcode_ok o8 /\
                         ntp4vc_ira_wtrans o8 =
                           ntp4vc_ira_to_wp
                             (ntp4vc_ira_hpost o7)) /\
                        (?o9:ntp4vc_ira_wcode.
                           (ntp4vc_ira_wcode_ok o9 /\
                            ntp4vc_ira_wtrans o9 =
                              ntp4vc_ira_rcompose
                                (ntp4vc_ira_wtrans o6)
                                (ntp4vc_ira_wtrans o8)) /\
                           ntp4vc_ira_wcode_ok o2 /\
                           ntp4vc_ira_wtrans o2 =
                             ntp4vc_ira_rcompose
                               (ntp4vc_ira_wtrans o4)
                               (ntp4vc_ira_wtrans o9))))))))`;;

let statement =
 `!e:ntp4vc_ira_expr.
  !r:int.
    ntp4vc_ira_compile_pre r e /\
    (!o2:ntp4vc_ira_wcode.
       ntp4vc_ira_compile_build r e o2
       ==>
       (ntp4vc_ira_wcode_ok o2 /\
        (!x:ntp4vc_ira_state.
           ntp4vc_ira_wtrans o2
             (ntp4vc_ira_expr_post e r x) x)) /\
       (!result:ntp4vc_ira_hcode.
          ntp4vc_ira_hcode_ok result /\
          ntp4vc_ira_hpost result = ntp4vc_ira_expr_post e r
          ==>
          ntp4vc_ira_hcode_ok result /\
          ntp4vc_ira_hpost result = ntp4vc_ira_expr_post e r))`;;
