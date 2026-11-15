(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/register_allocation_OptimalNumberOfRegisters_compileqtvc: the
  expression-compiler verification condition that uses the recursively
  computed minimal register requirement to choose evaluation order and
  spills to a stack when the finite register supply is exhausted. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  ora_expr =
    OraEvar 'addr
  | OraEneg ora_expr
  | OraEadd ora_expr ora_expr
End

Datatype:
  ora_instr =
    OraIload 'addr int
  | OraIneg int
  | OraIadd int int
  | OraIpush int
  | OraIpop int
End

Datatype:
  ora_state =
    OraState ('addr -> int) (int -> int) (int list)
End

val ora_mem_def = Define `
  ora_mem (OraState mem reg st) = mem`;

val ora_reg_def = Define `
  ora_reg (OraState mem reg st) = reg`;

val ora_stack_def = Define `
  ora_stack (OraState mem reg st) = st`;

val ora_eval_def = Define `
  (ora_eval (mem : 'addr -> int) (OraEvar x) = mem x) /\
  (ora_eval mem (OraEneg e) = -(ora_eval mem e)) /\
  (ora_eval mem (OraEadd e1 e2) =
     ora_eval mem e1 + ora_eval mem e2)`;

val ora_update_def = Define `
  ora_update (reg : int -> int) (r : int) (v : int) =
    \r' : int. if r' = r then v else reg r'`;

val ora_exec_def = Define `
  (ora_exec (OraIload x r) s =
     OraState
       (ora_mem s)
       (ora_update (ora_reg s) r (ora_mem s x))
       (ora_stack s)) /\
  (ora_exec (OraIneg r) s =
     OraState
       (ora_mem s)
       (ora_update (ora_reg s) r (-(ora_reg s r)))
       (ora_stack s)) /\
  (ora_exec (OraIadd r1 r2) s =
     OraState
       (ora_mem s)
       (ora_update
          (ora_reg s) r2
          (ora_reg s r1 + ora_reg s r2))
       (ora_stack s)) /\
  (ora_exec (OraIpush r) s =
     OraState
       (ora_mem s)
       (ora_reg s)
       (ora_reg s r :: ora_stack s)) /\
  (ora_exec (OraIpop r) s =
     case ora_stack s of
       [] => s
     | v :: st =>
         OraState
           (ora_mem s)
           (ora_update (ora_reg s) r v)
           st)`;

val ora_exec_list_def = Define `
  (ora_exec_list ([] : 'addr ora_instr list) s = s) /\
  (ora_exec_list (i :: code) s =
     ora_exec_list code (ora_exec i s))`;

val ora_expr_post_def = Define `
  ora_expr_post
    (e : 'addr ora_expr) (r : int)
    (s : 'addr ora_state) (s' : 'addr ora_state) <=>
    ora_mem s' = ora_mem s /\
    ora_reg s' r = ora_eval (ora_mem s) e /\
    ora_stack s' = ora_stack s /\
    (!r' : int.
       r' < r ==> ora_reg s' r' = ora_reg s r')`;

Datatype:
  ora_hcode =
    OraHcode
      (('addr ora_instr) list)
      ('addr ora_state -> 'addr ora_state -> bool)
End

Datatype:
  ora_wcode =
    OraWcode
      (('addr ora_state -> bool) -> 'addr ora_state -> bool)
      (('addr ora_instr) list)
End

val ora_hpost_def = Define `
  ora_hpost (OraHcode code pst) = pst`;

val ora_hcode_body_def = Define `
  ora_hcode_body (OraHcode code pst) = code`;

val ora_wtrans_def = Define `
  ora_wtrans (OraWcode trans code) = trans`;

val ora_wcode_body_def = Define `
  ora_wcode_body (OraWcode trans code) = code`;

val ora_hcode_ok_def = Define `
  ora_hcode_ok (hc : 'addr ora_hcode) <=>
    !s : 'addr ora_state.
      ora_hpost hc s
        (ora_exec_list (ora_hcode_body hc) s)`;

val ora_wcode_ok_def = Define `
  ora_wcode_ok (wc : 'addr ora_wcode) <=>
    !q : 'addr ora_state -> bool.
    !s : 'addr ora_state.
      ora_wtrans wc q s ==>
      q (ora_exec_list (ora_wcode_body wc) s)`;

val ora_to_wp_def = Define `
  ora_to_wp
    (pst : 'addr ora_state -> 'addr ora_state -> bool)
    (q : 'addr ora_state -> bool) (s1 : 'addr ora_state) <=>
    !s2 : 'addr ora_state. pst s1 s2 ==> q s2`;

val ora_rcompose_def = Define `
  ora_rcompose f g x = g (f x)`;

val ora_identity_def = Define `
  ora_identity (y : 'addr ora_state -> bool) = y`;

val ora_exec_closure_def = Define `
  ora_exec_closure
    (i : 'addr ora_instr) (s : 'addr ora_state) =
    ora_exec i s`;

val ora_n_def = Define `
  (ora_n (OraEvar x) = (1 : int)) /\
  (ora_n (OraEneg e) = ora_n e) /\
  (ora_n (OraEadd e1 e2) =
     let n1 = ora_n e1 in
     let n2 = ora_n e2 in
       if n1 = n2 then (1 : int) + n1
       else if n1 <= n2 then n2 else n1)`;

val ora_measure_def = Define `
  (ora_measure (OraEvar x) = (0 : int)) /\
  (ora_measure (OraEneg e) =
     (1 : int) + ora_measure e) /\
  (ora_measure (OraEadd e1 e2) =
     (1 : int) +
       if ora_n e2 <= ora_n e1 then
         ora_measure e1 + ora_measure e2
       else
         (1 : int) + ora_measure e1 + ora_measure e2)`;

val ora_compile_pre_def = Define `
  (ora_compile_pre k r (OraEvar x) <=>
     !o2 : 'addr ora_wcode.
       ora_wcode_ok o2 /\
       ora_wtrans o2 = ora_identity
       ==>
       ora_wcode_ok o2) /\
  (ora_compile_pre k r (OraEneg e1) <=>
     !o2 : 'addr ora_wcode.
       ora_wcode_ok o2 /\
       ora_wtrans o2 = ora_identity
       ==>
       ora_wcode_ok o2 /\
       (!o3 : 'addr ora_wcode.
          ora_wcode_ok o3 /\
          ora_wtrans o3 =
            ora_rcompose
              (ora_wtrans o2)
              (ora_rcompose
                (ora_exec_closure (OraIneg r)))
          ==>
          (((0 : int) <= ora_measure (OraEneg e1) /\
            ora_measure e1 < ora_measure (OraEneg e1)) /\
           (0 : int) <= r /\ r < k) /\
          (!o4 : 'addr ora_hcode.
             ora_hcode_ok o4 /\
             ora_hpost o4 = ora_expr_post e1 r
             ==>
             ora_hcode_ok o4 /\
             (!o5 : 'addr ora_wcode.
                ora_wcode_ok o5 /\
                ora_wtrans o5 =
                  ora_to_wp (ora_hpost o4)
                ==>
                ora_wcode_ok o5 /\
                ora_wcode_ok o3)))) /\
  (ora_compile_pre k r (OraEadd e1 e2) <=>
     if ora_n e2 <= ora_n e1 then
       if r < k - (1 : int) then (
         !o2 : 'addr ora_wcode.
           ora_wcode_ok o2 /\
           ora_wtrans o2 = ora_identity
           ==>
           ora_wcode_ok o2 /\
           (!o3 : 'addr ora_wcode.
              ora_wcode_ok o3 /\
              ora_wtrans o3 =
                ora_rcompose
                  (ora_wtrans o2)
                  (ora_rcompose
                    (ora_exec_closure
                      (OraIadd (r + (1 : int)) r)))
              ==>
              let o4 = r + (1 : int)
              in
                (((0 : int) <= ora_measure (OraEadd e1 e2) /\
                  ora_measure e2 < ora_measure (OraEadd e1 e2)) /\
                 (0 : int) <= o4 /\ o4 < k) /\
                (!o5 : 'addr ora_hcode.
                   ora_hcode_ok o5 /\
                   ora_hpost o5 = ora_expr_post e2 o4
                   ==>
                   ora_hcode_ok o5 /\
                   (!o6 : 'addr ora_wcode.
                      ora_wcode_ok o6 /\
                      ora_wtrans o6 =
                        ora_to_wp (ora_hpost o5)
                      ==>
                      (((0 : int) <= ora_measure (OraEadd e1 e2) /\
                        ora_measure e1 <
                          ora_measure (OraEadd e1 e2)) /\
                       (0 : int) <= r /\ r < k) /\
                      (!o7 : 'addr ora_hcode.
                         ora_hcode_ok o7 /\
                         ora_hpost o7 = ora_expr_post e1 r
                         ==>
                         ora_hcode_ok o7 /\
                         (!o8 : 'addr ora_wcode.
                            ora_wcode_ok o8 /\
                            ora_wtrans o8 =
                              ora_to_wp (ora_hpost o7)
                            ==>
                            (ora_wcode_ok o8 /\
                             ora_wcode_ok o6) /\
                            (!o9 : 'addr ora_wcode.
                               ora_wcode_ok o9 /\
                               ora_wtrans o9 =
                                 ora_rcompose
                                   (ora_wtrans o6)
                                   (ora_wtrans o8)
                               ==>
                               ora_wcode_ok o9 /\
                               ora_wcode_ok o3)))))))
       else (
         !o2 : 'addr ora_wcode.
           ora_wcode_ok o2 /\
           ora_wtrans o2 = ora_identity
           ==>
           ora_wcode_ok o2 /\
           (!o3 : 'addr ora_wcode.
              ora_wcode_ok o3 /\
              ora_wtrans o3 =
                ora_rcompose
                  (ora_wtrans o2)
                  (ora_rcompose
                    (ora_exec_closure
                      (OraIpop (k - (2 : int)))))
              ==>
              ora_wcode_ok o3 /\
              (!o4 : 'addr ora_wcode.
                 ora_wcode_ok o4 /\
                 ora_wtrans o4 =
                   ora_rcompose
                     (ora_wtrans o3)
                     (ora_rcompose
                       (ora_exec_closure
                         (OraIadd
                           (k - (2 : int))
                           (k - (1 : int)))))
                 ==>
                 let o5 = k - (1 : int)
                 in
                   (((0 : int) <= ora_measure (OraEadd e1 e2) /\
                     ora_measure e2 <
                       ora_measure (OraEadd e1 e2)) /\
                    (0 : int) <= o5 /\ o5 < k) /\
                   (!o6 : 'addr ora_hcode.
                      ora_hcode_ok o6 /\
                      ora_hpost o6 = ora_expr_post e2 o5
                      ==>
                      ora_hcode_ok o6 /\
                      (!o7 : 'addr ora_wcode.
                         ora_wcode_ok o7 /\
                         ora_wtrans o7 =
                           ora_to_wp (ora_hpost o6)
                         ==>
                         let o8 = k - (2 : int)
                         in
                           (((0 : int) <=
                               ora_measure (OraEadd e1 e2) /\
                             ora_measure e1 <
                               ora_measure (OraEadd e1 e2)) /\
                            (0 : int) <= o8 /\ o8 < k) /\
                           (!o9 : 'addr ora_hcode.
                              ora_hcode_ok o9 /\
                              ora_hpost o9 =
                                ora_expr_post e1 o8
                              ==>
                              ora_hcode_ok o9 /\
                              (!o10 : 'addr ora_wcode.
                                 ora_wcode_ok o10 /\
                                 ora_wtrans o10 =
                                   ora_to_wp (ora_hpost o9)
                                 ==>
                                 (ora_wcode_ok o10 /\
                                  ora_wcode_ok o7) /\
                                 (!o11 : 'addr ora_wcode.
                                    ora_wcode_ok o11 /\
                                    ora_wtrans o11 =
                                      ora_rcompose
                                        (ora_wtrans o7)
                                        (ora_wtrans o10)
                                    ==>
                                    (ora_wcode_ok o11 /\
                                     ora_wcode_ok o4) /\
                                    (!o12 : 'addr ora_wcode.
                                       ora_wcode_ok o12 /\
                                       ora_wtrans o12 =
                                         ora_rcompose
                                           (ora_wtrans o4)
                                           (ora_wtrans o11)
                                       ==>
                                       ora_wcode_ok o12)))))))))
     else
       let swapped = OraEadd e2 e1
       in
         (((0 : int) <= ora_measure (OraEadd e1 e2) /\
           ora_measure swapped < ora_measure (OraEadd e1 e2)) /\
          (0 : int) <= r /\ r < k) /\
         (!o3 : 'addr ora_hcode.
            ora_hcode_ok o3 /\
            ora_hpost o3 = ora_expr_post swapped r
            ==>
            ora_hcode_ok o3))`;

val ora_compile_build_def = Define `
  (ora_compile_build k r (OraEvar x) o2 <=>
     ?o3 : 'addr ora_wcode.
       (ora_wcode_ok o3 /\
        ora_wtrans o3 = ora_identity) /\
       ora_wcode_ok o2 /\
       ora_wtrans o2 =
         ora_rcompose
           (ora_wtrans o3)
           (ora_rcompose
             (ora_exec_closure (OraIload x r)))) /\
  (ora_compile_build k r (OraEneg e1) o2 <=>
     ?o3 : 'addr ora_wcode.
       (ora_wcode_ok o3 /\
        ora_wtrans o3 = ora_identity) /\
       (?o4 : 'addr ora_wcode.
          (ora_wcode_ok o4 /\
           ora_wtrans o4 =
             ora_rcompose
               (ora_wtrans o3)
               (ora_rcompose
                 (ora_exec_closure (OraIneg r)))) /\
          (?o5 : 'addr ora_hcode.
             (ora_hcode_ok o5 /\
              ora_hpost o5 = ora_expr_post e1 r) /\
             (?o6 : 'addr ora_wcode.
                (ora_wcode_ok o6 /\
                 ora_wtrans o6 =
                   ora_to_wp (ora_hpost o5)) /\
                ora_wcode_ok o2 /\
                ora_wtrans o2 =
                  ora_rcompose
                    (ora_wtrans o4)
                    (ora_wtrans o6))))) /\
  (ora_compile_build k r (OraEadd e1 e2) o2 <=>
     if ora_n e2 <= ora_n e1 then
       if r < k - (1 : int) then (
         ?o3 : 'addr ora_wcode.
           (ora_wcode_ok o3 /\
            ora_wtrans o3 = ora_identity) /\
           (?o4 : 'addr ora_wcode.
              (ora_wcode_ok o4 /\
               ora_wtrans o4 =
                 ora_rcompose
                   (ora_wtrans o3)
                   (ora_rcompose
                     (ora_exec_closure
                       (OraIadd (r + (1 : int)) r)))) /\
              (?o5 : 'addr ora_hcode.
                 (ora_hcode_ok o5 /\
                  ora_hpost o5 =
                    ora_expr_post e2 (r + (1 : int))) /\
                 (?o6 : 'addr ora_wcode.
                    (ora_wcode_ok o6 /\
                     ora_wtrans o6 =
                       ora_to_wp (ora_hpost o5)) /\
                    (?o7 : 'addr ora_hcode.
                       (ora_hcode_ok o7 /\
                        ora_hpost o7 =
                          ora_expr_post e1 r) /\
                       (?o8 : 'addr ora_wcode.
                          (ora_wcode_ok o8 /\
                           ora_wtrans o8 =
                             ora_to_wp (ora_hpost o7)) /\
                          (?o9 : 'addr ora_wcode.
                             (ora_wcode_ok o9 /\
                              ora_wtrans o9 =
                                ora_rcompose
                                  (ora_wtrans o6)
                                  (ora_wtrans o8)) /\
                             ora_wcode_ok o2 /\
                             ora_wtrans o2 =
                               ora_rcompose
                                 (ora_wtrans o4)
                                 (ora_wtrans o9))))))))
       else (
         ?o3 : 'addr ora_wcode.
           (ora_wcode_ok o3 /\
            ora_wtrans o3 = ora_identity) /\
           (?o4 : 'addr ora_wcode.
              (ora_wcode_ok o4 /\
               ora_wtrans o4 =
                 ora_rcompose
                   (ora_wtrans o3)
                   (ora_rcompose
                     (ora_exec_closure
                       (OraIpop (k - (2 : int)))))) /\
              (?o5 : 'addr ora_wcode.
                 (ora_wcode_ok o5 /\
                  ora_wtrans o5 =
                    ora_rcompose
                      (ora_wtrans o4)
                      (ora_rcompose
                        (ora_exec_closure
                          (OraIadd
                            (k - (2 : int))
                            (k - (1 : int)))))) /\
                 (?o6 : 'addr ora_hcode.
                    (ora_hcode_ok o6 /\
                     ora_hpost o6 =
                       ora_expr_post e2 (k - (1 : int))) /\
                    (?o7 : 'addr ora_wcode.
                       (ora_wcode_ok o7 /\
                        ora_wtrans o7 =
                          ora_to_wp (ora_hpost o6)) /\
                       (?o8 : 'addr ora_hcode.
                          (ora_hcode_ok o8 /\
                           ora_hpost o8 =
                             ora_expr_post e1 (k - (2 : int))) /\
                          (?o9 : 'addr ora_wcode.
                             (ora_wcode_ok o9 /\
                              ora_wtrans o9 =
                                ora_to_wp (ora_hpost o8)) /\
                             (?o10 : 'addr ora_wcode.
                                (ora_wcode_ok o10 /\
                                 ora_wtrans o10 =
                                   ora_rcompose
                                     (ora_wtrans o7)
                                     (ora_wtrans o9)) /\
                                (?o11 : 'addr ora_wcode.
                                   (ora_wcode_ok o11 /\
                                    ora_wtrans o11 =
                                      ora_rcompose
                                        (ora_wtrans o5)
                                        (ora_wtrans o10)) /\
                                   ora_wcode_ok o2 /\
                                   ora_wtrans o2 =
                                     ora_rcompose
                                       (ora_wtrans o11)
                                       (ora_rcompose
                                         (ora_exec_closure
                                           (OraIpush
                                             (k - (2 : int))))))))))))))
     else
       ?o3 : 'addr ora_hcode.
         (ora_hcode_ok o3 /\
          ora_hpost o3 =
            ora_expr_post (OraEadd e2 e1) r) /\
         ora_wcode_ok o2 /\
         ora_wtrans o2 =
           ora_to_wp (ora_hpost o3))`;

val register_allocation_OptimalNumberOfRegisters_compile_vc =
  ``!k : int.
      (2 : int) <= k
      ==>
      !r : int.
      !e : 'addr ora_expr.
        (0 : int) <= r
        ==>
        r < k
        ==>
        ora_compile_pre k r e /\
        (!o2 : 'addr ora_wcode.
           ora_compile_build k r e o2
           ==>
           (ora_wcode_ok o2 /\
            (!x : 'addr ora_state.
               ora_wtrans o2
                 (ora_expr_post e r x) x)) /\
           (!result : 'addr ora_hcode.
              ora_hcode_ok result /\
              ora_hpost result = ora_expr_post e r
              ==>
              ora_hcode_ok result /\
              ora_hpost result = ora_expr_post e r))``;
