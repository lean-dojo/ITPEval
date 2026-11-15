(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/register_allocation_FiniteNumberOfRegisters_compileqtvc: the
  finite-register expression compiler verification condition, including
  direct register allocation, stack spilling, and double-WP correctness.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  fra_expr =
    FraEvar 'addr
  | FraEneg fra_expr
  | FraEadd fra_expr fra_expr
End

Datatype:
  fra_instr =
    FraIload 'addr int
  | FraIneg int
  | FraIadd int int
  | FraIpush int
  | FraIpop int
End

Datatype:
  fra_state =
    FraState ('addr -> int) (int -> int) (int list)
End

val fra_mem_def = Define `
  fra_mem (FraState mem reg st) = mem`;

val fra_reg_def = Define `
  fra_reg (FraState mem reg st) = reg`;

val fra_stack_def = Define `
  fra_stack (FraState mem reg st) = st`;

val fra_eval_def = Define `
  (fra_eval (mem : 'addr -> int) (FraEvar x) = mem x) /\
  (fra_eval mem (FraEneg e) = -(fra_eval mem e)) /\
  (fra_eval mem (FraEadd e1 e2) =
     fra_eval mem e1 + fra_eval mem e2)`;

val fra_update_def = Define `
  fra_update (reg : int -> int) (r : int) (v : int) =
    \r' : int. if r' = r then v else reg r'`;

val fra_exec_def = Define `
  (fra_exec (FraIload x r) s =
     FraState
       (fra_mem s)
       (fra_update (fra_reg s) r (fra_mem s x))
       (fra_stack s)) /\
  (fra_exec (FraIneg r) s =
     FraState
       (fra_mem s)
       (fra_update (fra_reg s) r (-(fra_reg s r)))
       (fra_stack s)) /\
  (fra_exec (FraIadd r1 r2) s =
     FraState
       (fra_mem s)
       (fra_update
          (fra_reg s) r2
          (fra_reg s r1 + fra_reg s r2))
       (fra_stack s)) /\
  (fra_exec (FraIpush r) s =
     FraState
       (fra_mem s)
       (fra_reg s)
       (fra_reg s r :: fra_stack s)) /\
  (fra_exec (FraIpop r) s =
     case fra_stack s of
       [] => s
     | v :: st =>
         FraState
           (fra_mem s)
           (fra_update (fra_reg s) r v)
           st)`;

val fra_exec_list_def = Define `
  (fra_exec_list ([] : 'addr fra_instr list) s = s) /\
  (fra_exec_list (i :: code) s =
     fra_exec_list code (fra_exec i s))`;

val fra_expr_post_def = Define `
  fra_expr_post
    (e : 'addr fra_expr) (r : int)
    (s : 'addr fra_state) (s' : 'addr fra_state) <=>
    fra_mem s' = fra_mem s /\
    fra_reg s' r = fra_eval (fra_mem s) e /\
    fra_stack s' = fra_stack s /\
    (!r' : int.
       r' < r ==> fra_reg s' r' = fra_reg s r')`;

Datatype:
  fra_hcode =
    FraHcode
      (('addr fra_instr) list)
      ('addr fra_state -> 'addr fra_state -> bool)
End

Datatype:
  fra_wcode =
    FraWcode
      (('addr fra_state -> bool) -> 'addr fra_state -> bool)
      (('addr fra_instr) list)
End

val fra_hpost_def = Define `
  fra_hpost (FraHcode code pst) = pst`;

val fra_hcode_body_def = Define `
  fra_hcode_body (FraHcode code pst) = code`;

val fra_wtrans_def = Define `
  fra_wtrans (FraWcode trans code) = trans`;

val fra_wcode_body_def = Define `
  fra_wcode_body (FraWcode trans code) = code`;

val fra_hcode_ok_def = Define `
  fra_hcode_ok (hc : 'addr fra_hcode) <=>
    !s : 'addr fra_state.
      fra_hpost hc s
        (fra_exec_list (fra_hcode_body hc) s)`;

val fra_wcode_ok_def = Define `
  fra_wcode_ok (wc : 'addr fra_wcode) <=>
    !q : 'addr fra_state -> bool.
    !s : 'addr fra_state.
      fra_wtrans wc q s ==>
      q (fra_exec_list (fra_wcode_body wc) s)`;

val fra_to_wp_def = Define `
  fra_to_wp
    (pst : 'addr fra_state -> 'addr fra_state -> bool)
    (q : 'addr fra_state -> bool) (s1 : 'addr fra_state) <=>
    !s2 : 'addr fra_state. pst s1 s2 ==> q s2`;

val fra_rcompose_def = Define `
  fra_rcompose f g x = g (f x)`;

val fra_identity_def = Define `
  fra_identity (y : 'addr fra_state -> bool) = y`;

val fra_exec_closure_def = Define `
  fra_exec_closure
    (i : 'addr fra_instr) (s : 'addr fra_state) =
    fra_exec i s`;

val fra_direct_child_def = Define `
  (fra_direct_child (FraEvar x) child <=> F) /\
  (fra_direct_child (FraEneg e) child <=> e = child) /\
  (fra_direct_child (FraEadd e1 e2) child <=>
     e1 = child \/ e2 = child)`;

val fra_compile_pre_def = Define `
  (fra_compile_pre k r (FraEvar x) <=>
     !o2 : 'addr fra_wcode.
       fra_wcode_ok o2 /\
       fra_wtrans o2 = fra_identity
       ==>
       fra_wcode_ok o2) /\
  (fra_compile_pre k r (FraEneg e1) <=>
     !o2 : 'addr fra_wcode.
       fra_wcode_ok o2 /\
       fra_wtrans o2 = fra_identity
       ==>
       fra_wcode_ok o2 /\
       (!o3 : 'addr fra_wcode.
          fra_wcode_ok o3 /\
          fra_wtrans o3 =
            fra_rcompose
              (fra_wtrans o2)
              (fra_rcompose
                (fra_exec_closure (FraIneg r)))
          ==>
          (fra_direct_child (FraEneg e1) e1 /\
           (0 : int) <= r /\ r < k) /\
          (!o4 : 'addr fra_hcode.
             fra_hcode_ok o4 /\
             fra_hpost o4 = fra_expr_post e1 r
             ==>
             fra_hcode_ok o4 /\
             (!o5 : 'addr fra_wcode.
                fra_wcode_ok o5 /\
                fra_wtrans o5 =
                  fra_to_wp (fra_hpost o4)
                ==>
                fra_wcode_ok o5 /\
                fra_wcode_ok o3)))) /\
  (fra_compile_pre k r (FraEadd e1 e2) <=>
     if r < k - (1 : int) then (
       !o2 : 'addr fra_wcode.
         fra_wcode_ok o2 /\
         fra_wtrans o2 = fra_identity
         ==>
         fra_wcode_ok o2 /\
         (!o3 : 'addr fra_wcode.
            fra_wcode_ok o3 /\
            fra_wtrans o3 =
              fra_rcompose
                (fra_wtrans o2)
                (fra_rcompose
                  (fra_exec_closure
                    (FraIadd (r + (1 : int)) r)))
            ==>
            let o4 = r + (1 : int)
            in
              (fra_direct_child (FraEadd e1 e2) e2 /\
               (0 : int) <= o4 /\ o4 < k) /\
              (!o5 : 'addr fra_hcode.
                 fra_hcode_ok o5 /\
                 fra_hpost o5 = fra_expr_post e2 o4
                 ==>
                 fra_hcode_ok o5 /\
                 (!o6 : 'addr fra_wcode.
                    fra_wcode_ok o6 /\
                    fra_wtrans o6 =
                      fra_to_wp (fra_hpost o5)
                    ==>
                    (fra_direct_child (FraEadd e1 e2) e1 /\
                     (0 : int) <= r /\ r < k) /\
                    (!o7 : 'addr fra_hcode.
                       fra_hcode_ok o7 /\
                       fra_hpost o7 = fra_expr_post e1 r
                       ==>
                       fra_hcode_ok o7 /\
                       (!o8 : 'addr fra_wcode.
                          fra_wcode_ok o8 /\
                          fra_wtrans o8 =
                            fra_to_wp (fra_hpost o7)
                          ==>
                          (fra_wcode_ok o8 /\
                           fra_wcode_ok o6) /\
                          (!o9 : 'addr fra_wcode.
                             fra_wcode_ok o9 /\
                             fra_wtrans o9 =
                               fra_rcompose
                                 (fra_wtrans o6)
                                 (fra_wtrans o8)
                             ==>
                             fra_wcode_ok o9 /\
                             fra_wcode_ok o3)))))))
     else (
       !o2 : 'addr fra_wcode.
         fra_wcode_ok o2 /\
         fra_wtrans o2 = fra_identity
         ==>
         fra_wcode_ok o2 /\
         (!o3 : 'addr fra_wcode.
            fra_wcode_ok o3 /\
            fra_wtrans o3 =
              fra_rcompose
                (fra_wtrans o2)
                (fra_rcompose
                  (fra_exec_closure
                    (FraIpop (k - (2 : int)))))
            ==>
            fra_wcode_ok o3 /\
            (!o4 : 'addr fra_wcode.
               fra_wcode_ok o4 /\
               fra_wtrans o4 =
                 fra_rcompose
                   (fra_wtrans o3)
                   (fra_rcompose
                     (fra_exec_closure
                       (FraIadd
                         (k - (2 : int))
                         (k - (1 : int)))))
               ==>
               let o5 = k - (1 : int)
               in
                 (fra_direct_child (FraEadd e1 e2) e2 /\
                  (0 : int) <= o5 /\ o5 < k) /\
                 (!o6 : 'addr fra_hcode.
                    fra_hcode_ok o6 /\
                    fra_hpost o6 =
                      fra_expr_post e2 o5
                    ==>
                    fra_hcode_ok o6 /\
                    (!o7 : 'addr fra_wcode.
                       fra_wcode_ok o7 /\
                       fra_wtrans o7 =
                         fra_to_wp (fra_hpost o6)
                       ==>
                       let o8 = k - (2 : int)
                       in
                         (fra_direct_child (FraEadd e1 e2) e1 /\
                          (0 : int) <= o8 /\ o8 < k) /\
                         (!o9 : 'addr fra_hcode.
                            fra_hcode_ok o9 /\
                            fra_hpost o9 =
                              fra_expr_post e1 o8
                            ==>
                            fra_hcode_ok o9 /\
                            (!o10 : 'addr fra_wcode.
                               fra_wcode_ok o10 /\
                               fra_wtrans o10 =
                                 fra_to_wp (fra_hpost o9)
                               ==>
                               (fra_wcode_ok o10 /\
                                fra_wcode_ok o7) /\
                               (!o11 : 'addr fra_wcode.
                                  fra_wcode_ok o11 /\
                                  fra_wtrans o11 =
                                    fra_rcompose
                                      (fra_wtrans o7)
                                      (fra_wtrans o10)
                                  ==>
                                  (fra_wcode_ok o11 /\
                                   fra_wcode_ok o4) /\
                                  (!o12 : 'addr fra_wcode.
                                     fra_wcode_ok o12 /\
                                     fra_wtrans o12 =
                                       fra_rcompose
                                         (fra_wtrans o4)
                                         (fra_wtrans o11)
                                     ==>
                                     fra_wcode_ok o12))))))))))`;

val fra_compile_build_def = Define `
  (fra_compile_build k r (FraEvar x) o2 <=>
     ?o3 : 'addr fra_wcode.
       (fra_wcode_ok o3 /\
        fra_wtrans o3 = fra_identity) /\
       fra_wcode_ok o2 /\
       fra_wtrans o2 =
         fra_rcompose
           (fra_wtrans o3)
           (fra_rcompose
             (fra_exec_closure (FraIload x r)))) /\
  (fra_compile_build k r (FraEneg e1) o2 <=>
     ?o3 : 'addr fra_wcode.
       (fra_wcode_ok o3 /\
        fra_wtrans o3 = fra_identity) /\
       (?o4 : 'addr fra_wcode.
          (fra_wcode_ok o4 /\
           fra_wtrans o4 =
             fra_rcompose
               (fra_wtrans o3)
               (fra_rcompose
                 (fra_exec_closure (FraIneg r)))) /\
          (?o5 : 'addr fra_hcode.
             (fra_hcode_ok o5 /\
              fra_hpost o5 = fra_expr_post e1 r) /\
             (?o6 : 'addr fra_wcode.
                (fra_wcode_ok o6 /\
                 fra_wtrans o6 =
                   fra_to_wp (fra_hpost o5)) /\
                fra_wcode_ok o2 /\
                fra_wtrans o2 =
                  fra_rcompose
                    (fra_wtrans o4)
                    (fra_wtrans o6))))) /\
  (fra_compile_build k r (FraEadd e1 e2) o2 <=>
     if r < k - (1 : int) then (
       ?o3 : 'addr fra_wcode.
         (fra_wcode_ok o3 /\
          fra_wtrans o3 = fra_identity) /\
         (?o4 : 'addr fra_wcode.
            (fra_wcode_ok o4 /\
             fra_wtrans o4 =
               fra_rcompose
                 (fra_wtrans o3)
                 (fra_rcompose
                   (fra_exec_closure
                     (FraIadd (r + (1 : int)) r)))) /\
            (?o5 : 'addr fra_hcode.
               (fra_hcode_ok o5 /\
                fra_hpost o5 =
                  fra_expr_post e2 (r + (1 : int))) /\
               (?o6 : 'addr fra_wcode.
                  (fra_wcode_ok o6 /\
                   fra_wtrans o6 =
                     fra_to_wp (fra_hpost o5)) /\
                  (?o7 : 'addr fra_hcode.
                     (fra_hcode_ok o7 /\
                      fra_hpost o7 =
                        fra_expr_post e1 r) /\
                     (?o8 : 'addr fra_wcode.
                        (fra_wcode_ok o8 /\
                         fra_wtrans o8 =
                           fra_to_wp (fra_hpost o7)) /\
                        (?o9 : 'addr fra_wcode.
                           (fra_wcode_ok o9 /\
                            fra_wtrans o9 =
                              fra_rcompose
                                (fra_wtrans o6)
                                (fra_wtrans o8)) /\
                           fra_wcode_ok o2 /\
                           fra_wtrans o2 =
                             fra_rcompose
                               (fra_wtrans o4)
                               (fra_wtrans o9))))))))
     else (
       ?o3 : 'addr fra_wcode.
         (fra_wcode_ok o3 /\
          fra_wtrans o3 = fra_identity) /\
         (?o4 : 'addr fra_wcode.
            (fra_wcode_ok o4 /\
             fra_wtrans o4 =
               fra_rcompose
                 (fra_wtrans o3)
                 (fra_rcompose
                   (fra_exec_closure
                     (FraIpop (k - (2 : int)))))) /\
            (?o5 : 'addr fra_wcode.
               (fra_wcode_ok o5 /\
                fra_wtrans o5 =
                  fra_rcompose
                    (fra_wtrans o4)
                    (fra_rcompose
                      (fra_exec_closure
                        (FraIadd
                          (k - (2 : int))
                          (k - (1 : int)))))) /\
               (?o6 : 'addr fra_hcode.
                  (fra_hcode_ok o6 /\
                   fra_hpost o6 =
                     fra_expr_post e2 (k - (1 : int))) /\
                  (?o7 : 'addr fra_wcode.
                     (fra_wcode_ok o7 /\
                      fra_wtrans o7 =
                        fra_to_wp (fra_hpost o6)) /\
                     (?o8 : 'addr fra_hcode.
                        (fra_hcode_ok o8 /\
                         fra_hpost o8 =
                           fra_expr_post e1 (k - (2 : int))) /\
                        (?o9 : 'addr fra_wcode.
                           (fra_wcode_ok o9 /\
                            fra_wtrans o9 =
                              fra_to_wp (fra_hpost o8)) /\
                           (?o10 : 'addr fra_wcode.
                              (fra_wcode_ok o10 /\
                               fra_wtrans o10 =
                                 fra_rcompose
                                   (fra_wtrans o7)
                                   (fra_wtrans o9)) /\
                              (?o11 : 'addr fra_wcode.
                                 (fra_wcode_ok o11 /\
                                  fra_wtrans o11 =
                                    fra_rcompose
                                      (fra_wtrans o5)
                                      (fra_wtrans o10)) /\
                                 fra_wcode_ok o2 /\
                                 fra_wtrans o2 =
                                   fra_rcompose
                                     (fra_wtrans o11)
                                     (fra_rcompose
                                       (fra_exec_closure
                                         (FraIpush
                                           (k - (2 : int)))))))))))))))`;

val register_allocation_FiniteNumberOfRegisters_compile_vc =
  ``!k : int.
      (2 : int) <= k
      ==>
      !r : int.
      !e : 'addr fra_expr.
        (0 : int) <= r
        ==>
        r < k
        ==>
        fra_compile_pre k r e /\
        (!o2 : 'addr fra_wcode.
           fra_compile_build k r e o2
           ==>
           (fra_wcode_ok o2 /\
            (!x : 'addr fra_state.
               fra_wtrans o2
                 (fra_expr_post e r x) x)) /\
           (!result : 'addr fra_hcode.
              fra_hcode_ok result /\
              fra_hpost result = fra_expr_post e r
              ==>
              fra_hcode_ok result /\
              fra_hpost result = fra_expr_post e r))``;
