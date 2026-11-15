(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/register_allocation_InfinityOfRegisters_compileqtvc: the
  unbounded-register expression compiler verification condition, including
  recursive register allocation and double-WP correctness. This file contains
  no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  ira_expr =
    IraEvar 'addr
  | IraEneg ira_expr
  | IraEadd ira_expr ira_expr
End

Datatype:
  ira_instr =
    IraIload 'addr int
  | IraIneg int
  | IraIadd int int
  | IraIpush int
  | IraIpop int
End

Datatype:
  ira_state =
    IraState ('addr -> int) (int -> int) (int list)
End

val ira_mem_def = Define `
  ira_mem (IraState mem reg st) = mem`;

val ira_reg_def = Define `
  ira_reg (IraState mem reg st) = reg`;

val ira_stack_def = Define `
  ira_stack (IraState mem reg st) = st`;

val ira_eval_def = Define `
  (ira_eval (mem : 'addr -> int) (IraEvar x) = mem x) /\
  (ira_eval mem (IraEneg e) = -(ira_eval mem e)) /\
  (ira_eval mem (IraEadd e1 e2) =
     ira_eval mem e1 + ira_eval mem e2)`;

val ira_update_def = Define `
  ira_update (reg : int -> int) (r : int) (v : int) =
    \r' : int. if r' = r then v else reg r'`;

val ira_exec_def = Define `
  (ira_exec (IraIload x r) s =
     IraState
       (ira_mem s)
       (ira_update (ira_reg s) r (ira_mem s x))
       (ira_stack s)) /\
  (ira_exec (IraIneg r) s =
     IraState
       (ira_mem s)
       (ira_update (ira_reg s) r (-(ira_reg s r)))
       (ira_stack s)) /\
  (ira_exec (IraIadd r1 r2) s =
     IraState
       (ira_mem s)
       (ira_update
          (ira_reg s) r2
          (ira_reg s r1 + ira_reg s r2))
       (ira_stack s)) /\
  (ira_exec (IraIpush r) s =
     IraState
       (ira_mem s)
       (ira_reg s)
       (ira_reg s r :: ira_stack s)) /\
  (ira_exec (IraIpop r) s =
     case ira_stack s of
       [] => s
     | v :: st =>
         IraState
           (ira_mem s)
           (ira_update (ira_reg s) r v)
           st)`;

val ira_exec_list_def = Define `
  (ira_exec_list ([] : 'addr ira_instr list) s = s) /\
  (ira_exec_list (i :: code) s =
     ira_exec_list code (ira_exec i s))`;

val ira_expr_post_def = Define `
  ira_expr_post
    (e : 'addr ira_expr) (r : int)
    (s : 'addr ira_state) (s' : 'addr ira_state) <=>
    ira_mem s' = ira_mem s /\
    ira_reg s' r = ira_eval (ira_mem s) e /\
    ira_stack s' = ira_stack s /\
    (!r' : int.
       r' < r ==> ira_reg s' r' = ira_reg s r')`;

Datatype:
  ira_hcode =
    IraHcode
      (('addr ira_instr) list)
      ('addr ira_state -> 'addr ira_state -> bool)
End

Datatype:
  ira_wcode =
    IraWcode
      (('addr ira_state -> bool) -> 'addr ira_state -> bool)
      (('addr ira_instr) list)
End

val ira_hpost_def = Define `
  ira_hpost (IraHcode code pst) = pst`;

val ira_hcode_body_def = Define `
  ira_hcode_body (IraHcode code pst) = code`;

val ira_wtrans_def = Define `
  ira_wtrans (IraWcode trans code) = trans`;

val ira_wcode_body_def = Define `
  ira_wcode_body (IraWcode trans code) = code`;

val ira_hcode_ok_def = Define `
  ira_hcode_ok (hc : 'addr ira_hcode) <=>
    !s : 'addr ira_state.
      ira_hpost hc s
        (ira_exec_list (ira_hcode_body hc) s)`;

val ira_wcode_ok_def = Define `
  ira_wcode_ok (wc : 'addr ira_wcode) <=>
    !q : 'addr ira_state -> bool.
    !s : 'addr ira_state.
      ira_wtrans wc q s ==>
      q (ira_exec_list (ira_wcode_body wc) s)`;

val ira_to_wp_def = Define `
  ira_to_wp
    (pst : 'addr ira_state -> 'addr ira_state -> bool)
    (q : 'addr ira_state -> bool) (s1 : 'addr ira_state) <=>
    !s2 : 'addr ira_state. pst s1 s2 ==> q s2`;

val ira_rcompose_def = Define `
  ira_rcompose f g x = g (f x)`;

val ira_identity_def = Define `
  ira_identity (y : 'addr ira_state -> bool) = y`;

val ira_exec_closure_def = Define `
  ira_exec_closure
    (i : 'addr ira_instr) (s : 'addr ira_state) =
    ira_exec i s`;

val ira_direct_child_def = Define `
  (ira_direct_child (IraEvar x) child <=> F) /\
  (ira_direct_child (IraEneg e) child <=> e = child) /\
  (ira_direct_child (IraEadd e1 e2) child <=>
     e1 = child \/ e2 = child)`;

val ira_compile_pre_def = Define `
  (ira_compile_pre r (IraEvar x) <=>
     !o2 : 'addr ira_wcode.
       ira_wcode_ok o2 /\
       ira_wtrans o2 = ira_identity
       ==>
       ira_wcode_ok o2) /\
  (ira_compile_pre r (IraEneg e1) <=>
     !o2 : 'addr ira_wcode.
       ira_wcode_ok o2 /\
       ira_wtrans o2 = ira_identity
       ==>
       ira_wcode_ok o2 /\
       (!o3 : 'addr ira_wcode.
          ira_wcode_ok o3 /\
          ira_wtrans o3 =
            ira_rcompose
              (ira_wtrans o2)
              (ira_rcompose
                (ira_exec_closure (IraIneg r)))
          ==>
          ira_direct_child (IraEneg e1) e1 /\
          (!o4 : 'addr ira_hcode.
             ira_hcode_ok o4 /\
             ira_hpost o4 = ira_expr_post e1 r
             ==>
             ira_hcode_ok o4 /\
             (!o5 : 'addr ira_wcode.
                ira_wcode_ok o5 /\
                ira_wtrans o5 =
                  ira_to_wp (ira_hpost o4)
                ==>
                ira_wcode_ok o5 /\
                ira_wcode_ok o3)))) /\
  (ira_compile_pre r (IraEadd e1 e2) <=>
     !o2 : 'addr ira_wcode.
       ira_wcode_ok o2 /\
       ira_wtrans o2 = ira_identity
       ==>
       ira_wcode_ok o2 /\
       (!o3 : 'addr ira_wcode.
          ira_wcode_ok o3 /\
          ira_wtrans o3 =
            ira_rcompose
              (ira_wtrans o2)
              (ira_rcompose
                (ira_exec_closure
                  (IraIadd (r + (1 : int)) r)))
          ==>
          ira_direct_child (IraEadd e1 e2) e2 /\
          (!o4 : 'addr ira_hcode.
             ira_hcode_ok o4 /\
             ira_hpost o4 =
               ira_expr_post e2 (r + (1 : int))
             ==>
             ira_hcode_ok o4 /\
             (!o5 : 'addr ira_wcode.
                ira_wcode_ok o5 /\
                ira_wtrans o5 =
                  ira_to_wp (ira_hpost o4)
                ==>
                ira_direct_child (IraEadd e1 e2) e1 /\
                (!o6 : 'addr ira_hcode.
                   ira_hcode_ok o6 /\
                   ira_hpost o6 = ira_expr_post e1 r
                   ==>
                   ira_hcode_ok o6 /\
                   (!o7 : 'addr ira_wcode.
                      ira_wcode_ok o7 /\
                      ira_wtrans o7 =
                        ira_to_wp (ira_hpost o6)
                      ==>
                      (ira_wcode_ok o7 /\
                       ira_wcode_ok o5) /\
                      (!o8 : 'addr ira_wcode.
                         ira_wcode_ok o8 /\
                         ira_wtrans o8 =
                           ira_rcompose
                             (ira_wtrans o5)
                             (ira_wtrans o7)
                         ==>
                         ira_wcode_ok o8 /\
                         ira_wcode_ok o3)))))))`;

val ira_compile_build_def = Define `
  (ira_compile_build r (IraEvar x) o2 <=>
     ?o3 : 'addr ira_wcode.
       (ira_wcode_ok o3 /\
        ira_wtrans o3 = ira_identity) /\
       ira_wcode_ok o2 /\
       ira_wtrans o2 =
         ira_rcompose
           (ira_wtrans o3)
           (ira_rcompose
             (ira_exec_closure (IraIload x r)))) /\
  (ira_compile_build r (IraEneg e1) o2 <=>
     ?o3 : 'addr ira_wcode.
       (ira_wcode_ok o3 /\
        ira_wtrans o3 = ira_identity) /\
       (?o4 : 'addr ira_wcode.
          (ira_wcode_ok o4 /\
           ira_wtrans o4 =
             ira_rcompose
               (ira_wtrans o3)
               (ira_rcompose
                 (ira_exec_closure (IraIneg r)))) /\
          (?o5 : 'addr ira_hcode.
             (ira_hcode_ok o5 /\
              ira_hpost o5 = ira_expr_post e1 r) /\
             (?o6 : 'addr ira_wcode.
                (ira_wcode_ok o6 /\
                 ira_wtrans o6 =
                   ira_to_wp (ira_hpost o5)) /\
                ira_wcode_ok o2 /\
                ira_wtrans o2 =
                  ira_rcompose
                    (ira_wtrans o4)
                    (ira_wtrans o6))))) /\
  (ira_compile_build r (IraEadd e1 e2) o2 <=>
     ?o3 : 'addr ira_wcode.
       (ira_wcode_ok o3 /\
        ira_wtrans o3 = ira_identity) /\
       (?o4 : 'addr ira_wcode.
          (ira_wcode_ok o4 /\
           ira_wtrans o4 =
             ira_rcompose
               (ira_wtrans o3)
               (ira_rcompose
                 (ira_exec_closure
                   (IraIadd (r + (1 : int)) r)))) /\
          (?o5 : 'addr ira_hcode.
             (ira_hcode_ok o5 /\
              ira_hpost o5 =
                ira_expr_post e2 (r + (1 : int))) /\
             (?o6 : 'addr ira_wcode.
                (ira_wcode_ok o6 /\
                 ira_wtrans o6 =
                   ira_to_wp (ira_hpost o5)) /\
                (?o7 : 'addr ira_hcode.
                   (ira_hcode_ok o7 /\
                    ira_hpost o7 = ira_expr_post e1 r) /\
                   (?o8 : 'addr ira_wcode.
                      (ira_wcode_ok o8 /\
                       ira_wtrans o8 =
                         ira_to_wp (ira_hpost o7)) /\
                      (?o9 : 'addr ira_wcode.
                         (ira_wcode_ok o9 /\
                          ira_wtrans o9 =
                            ira_rcompose
                              (ira_wtrans o6)
                              (ira_wtrans o8)) /\
                         ira_wcode_ok o2 /\
                         ira_wtrans o2 =
                           ira_rcompose
                             (ira_wtrans o4)
                             (ira_wtrans o9))))))))`;

val register_allocation_InfinityOfRegisters_compile_vc =
  ``!r : int.
    !e : 'addr ira_expr.
      ira_compile_pre r e /\
      (!o2 : 'addr ira_wcode.
         ira_compile_build r e o2
         ==>
         (ira_wcode_ok o2 /\
          (!x : 'addr ira_state.
             ira_wtrans o2
               (ira_expr_post e r x) x)) /\
         (!result : 'addr ira_hcode.
            ira_hcode_ok result /\
            ira_hpost result = ira_expr_post e r
            ==>
            ira_hcode_ok result /\
            ira_hpost result = ira_expr_post e r))``;
