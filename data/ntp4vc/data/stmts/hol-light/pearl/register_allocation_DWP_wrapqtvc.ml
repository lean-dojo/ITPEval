(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/register_allocation_DWP_wrapqtvc: the double-weakest-precondition
  register-allocation wrapping verification condition, converting well-formed
  weakest-precondition code into executable code satisfying its binary
  postcondition. This file contains no proof.
*)

new_type ("ntp4vc_ra_addr",0);;

let ntp4vc_ra_instr_INDUCT,ntp4vc_ra_instr_RECURSION =
  define_type
   "ntp4vc_ra_instr =
      NTP4VC_RA_Iload ntp4vc_ra_addr int
    | NTP4VC_RA_Ineg int
    | NTP4VC_RA_Iadd int int
    | NTP4VC_RA_Ipush int
    | NTP4VC_RA_Ipop int";;

let ntp4vc_ra_state_INDUCT,ntp4vc_ra_state_RECURSION =
  define_type
   "ntp4vc_ra_state =
      NTP4VC_RA_State
        (ntp4vc_ra_addr->int) (int->int) (int list)";;

let ntp4vc_ra_update = new_definition
 `ntp4vc_ra_update (reg:int->int) (r:int) (v:int) =
    \r':int. if r' = r then v else reg r'`;;

let ntp4vc_ra_mem =
  new_recursive_definition ntp4vc_ra_state_RECURSION
   `ntp4vc_ra_mem (NTP4VC_RA_State mem reg st) = mem`;;

let ntp4vc_ra_reg =
  new_recursive_definition ntp4vc_ra_state_RECURSION
   `ntp4vc_ra_reg (NTP4VC_RA_State mem reg st) = reg`;;

let ntp4vc_ra_stack =
  new_recursive_definition ntp4vc_ra_state_RECURSION
   `ntp4vc_ra_stack (NTP4VC_RA_State mem reg st) = st`;;

let ntp4vc_ra_exec =
  new_recursive_definition ntp4vc_ra_instr_RECURSION
   `(!x:ntp4vc_ra_addr.
     !r:int.
     !s:ntp4vc_ra_state.
       ntp4vc_ra_exec (NTP4VC_RA_Iload x r) s =
       NTP4VC_RA_State
         (ntp4vc_ra_mem s)
         (ntp4vc_ra_update (ntp4vc_ra_reg s) r (ntp4vc_ra_mem s x))
         (ntp4vc_ra_stack s)) /\
    (!r:int.
     !s:ntp4vc_ra_state.
       ntp4vc_ra_exec (NTP4VC_RA_Ineg r) s =
       NTP4VC_RA_State
         (ntp4vc_ra_mem s)
         (ntp4vc_ra_update
           (ntp4vc_ra_reg s) r (--(ntp4vc_ra_reg s r)))
         (ntp4vc_ra_stack s)) /\
    (!r1 r2:int.
     !s:ntp4vc_ra_state.
       ntp4vc_ra_exec (NTP4VC_RA_Iadd r1 r2) s =
       NTP4VC_RA_State
         (ntp4vc_ra_mem s)
         (ntp4vc_ra_update
           (ntp4vc_ra_reg s) r2
           (ntp4vc_ra_reg s r1 + ntp4vc_ra_reg s r2))
         (ntp4vc_ra_stack s)) /\
    (!r:int.
     !s:ntp4vc_ra_state.
       ntp4vc_ra_exec (NTP4VC_RA_Ipush r) s =
       NTP4VC_RA_State
         (ntp4vc_ra_mem s)
         (ntp4vc_ra_reg s)
         (CONS (ntp4vc_ra_reg s r) (ntp4vc_ra_stack s))) /\
    (!r:int.
     !s:ntp4vc_ra_state.
       ntp4vc_ra_exec (NTP4VC_RA_Ipop r) s =
       if ntp4vc_ra_stack s = [] then
         s
       else
         NTP4VC_RA_State
           (ntp4vc_ra_mem s)
           (ntp4vc_ra_update
             (ntp4vc_ra_reg s) r (HD (ntp4vc_ra_stack s)))
           (TL (ntp4vc_ra_stack s)))`;;

let ntp4vc_ra_exec_list =
  new_recursive_definition list_RECURSION
   `(!s:ntp4vc_ra_state.
       ntp4vc_ra_exec_list ([]:ntp4vc_ra_instr list) s = s) /\
    (!i:ntp4vc_ra_instr.
     !code:ntp4vc_ra_instr list.
     !s:ntp4vc_ra_state.
       ntp4vc_ra_exec_list (CONS i code) s =
       ntp4vc_ra_exec_list code (ntp4vc_ra_exec i s))`;;

let ntp4vc_ra_hcode_INDUCT,ntp4vc_ra_hcode_RECURSION =
  define_type
   "ntp4vc_ra_hcode =
      NTP4VC_RA_Hcode
        (ntp4vc_ra_instr list)
        (ntp4vc_ra_state->ntp4vc_ra_state->bool)";;

let ntp4vc_ra_wcode_INDUCT,ntp4vc_ra_wcode_RECURSION =
  define_type
   "ntp4vc_ra_wcode =
      NTP4VC_RA_Wcode
        ((ntp4vc_ra_state->bool)->ntp4vc_ra_state->bool)
        (ntp4vc_ra_instr list)";;

let ntp4vc_ra_wtrans =
  new_recursive_definition ntp4vc_ra_wcode_RECURSION
   `ntp4vc_ra_wtrans (NTP4VC_RA_Wcode trans code) = trans`;;

let ntp4vc_ra_wcode_body =
  new_recursive_definition ntp4vc_ra_wcode_RECURSION
   `ntp4vc_ra_wcode_body (NTP4VC_RA_Wcode trans code) = code`;;

let ntp4vc_ra_hcode_ok =
  new_recursive_definition ntp4vc_ra_hcode_RECURSION
   `ntp4vc_ra_hcode_ok (NTP4VC_RA_Hcode code pst) <=>
      !s:ntp4vc_ra_state.
        pst s (ntp4vc_ra_exec_list code s)`;;

let ntp4vc_ra_wcode_ok =
  new_recursive_definition ntp4vc_ra_wcode_RECURSION
   `ntp4vc_ra_wcode_ok (NTP4VC_RA_Wcode trans code) <=>
      !q:ntp4vc_ra_state->bool.
      !s:ntp4vc_ra_state.
        trans q s
        ==> q (ntp4vc_ra_exec_list code s)`;;

let statement =
 `!wc:ntp4vc_ra_wcode.
  !pst:ntp4vc_ra_state->ntp4vc_ra_state->bool.
    ntp4vc_ra_wcode_ok wc
    ==>
    (!x:ntp4vc_ra_state.
       ntp4vc_ra_wtrans wc (pst x) x)
    ==>
    ntp4vc_ra_hcode_ok
      (NTP4VC_RA_Hcode (ntp4vc_ra_wcode_body wc) pst)`;;
