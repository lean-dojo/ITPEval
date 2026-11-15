(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/register_allocation_DWP_wrapqtvc: the double-weakest-precondition
  register-allocation wrapping verification condition, converting sound
  weakest-precondition code into executable code satisfying its supplied
  binary state postcondition. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  ra_instr =
    RaIload 'addr int
  | RaIneg int
  | RaIadd int int
  | RaIpush int
  | RaIpop int
End

Datatype:
  ra_state =
    RaState ('addr -> int) (int -> int) (int list)
End

val ra_mem_def = Define `
  ra_mem (RaState mem reg st) = mem`;

val ra_reg_def = Define `
  ra_reg (RaState mem reg st) = reg`;

val ra_stack_def = Define `
  ra_stack (RaState mem reg st) = st`;

val ra_update_def = Define `
  ra_update (reg : int -> int) (r : int) (v : int) =
    \r' : int. if r' = r then v else reg r'`;

val ra_exec_def = Define `
  (ra_exec (RaIload x r) s =
     RaState
       (ra_mem s)
       (ra_update (ra_reg s) r (ra_mem s x))
       (ra_stack s)) /\
  (ra_exec (RaIneg r) s =
     RaState
       (ra_mem s)
       (ra_update (ra_reg s) r (-(ra_reg s r)))
       (ra_stack s)) /\
  (ra_exec (RaIadd r1 r2) s =
     RaState
       (ra_mem s)
       (ra_update
          (ra_reg s) r2
          (ra_reg s r1 + ra_reg s r2))
       (ra_stack s)) /\
  (ra_exec (RaIpush r) s =
     RaState
       (ra_mem s)
       (ra_reg s)
       (ra_reg s r :: ra_stack s)) /\
  (ra_exec (RaIpop r) s =
     case ra_stack s of
       [] => s
     | v :: st =>
         RaState
           (ra_mem s)
           (ra_update (ra_reg s) r v)
           st)`;

val ra_exec_list_def = Define `
  (ra_exec_list ([] : 'addr ra_instr list) s = s) /\
  (ra_exec_list (i :: code) s =
     ra_exec_list code (ra_exec i s))`;

Datatype:
  ra_hcode =
    RaHcode
      (('addr ra_instr) list)
      ('addr ra_state -> 'addr ra_state -> bool)
End

Datatype:
  ra_wcode =
    RaWcode
      (('addr ra_state -> bool) -> 'addr ra_state -> bool)
      (('addr ra_instr) list)
End

val ra_wtrans_def = Define `
  ra_wtrans (RaWcode trans code) = trans`;

val ra_wcode_body_def = Define `
  ra_wcode_body (RaWcode trans code) = code`;

val ra_hcode_ok_def = Define `
  ra_hcode_ok (RaHcode code pst) <=>
    !s : 'addr ra_state.
      pst s (ra_exec_list code s)`;

val ra_wcode_ok_def = Define `
  ra_wcode_ok (RaWcode trans code) <=>
    !q : 'addr ra_state -> bool.
    !s : 'addr ra_state.
      trans q s ==>
      q (ra_exec_list code s)`;

val register_allocation_DWP_wrap_vc =
  ``!wc : 'addr ra_wcode.
    !pst : 'addr ra_state -> 'addr ra_state -> bool.
      ra_wcode_ok wc ==>
      (!x : 'addr ra_state.
         ra_wtrans wc (pst x) x) ==>
      ra_hcode_ok
        (RaHcode (ra_wcode_body wc) pst)``;
