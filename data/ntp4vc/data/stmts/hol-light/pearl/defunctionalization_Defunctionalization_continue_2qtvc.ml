(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/defunctionalization_Defunctionalization_continue_2qtvc: a
  defunctionalized continuation-step verification condition relating
  structural size decrease to continuation evaluation. This file contains
  no proof.
*)

let ntp4vc_defun_expr_INDUCT,ntp4vc_defun_expr_RECURSION = define_type
  "ntp4vc_defun_expr =
       NTP4VCDefunCte int
     | NTP4VCDefunSub ntp4vc_defun_expr ntp4vc_defun_expr";;

let ntp4vc_defun_cont_INDUCT,ntp4vc_defun_cont_RECURSION = define_type
  "ntp4vc_defun_cont =
       NTP4VCDefunA1 ntp4vc_defun_expr ntp4vc_defun_cont
     | NTP4VCDefunA2 int ntp4vc_defun_cont
     | NTP4VCDefunI";;

let ntp4vc_defun_eval_expr =
  new_recursive_definition ntp4vc_defun_expr_RECURSION
   `(!n:int.
       ntp4vc_defun_eval_expr (NTP4VCDefunCte n) = n) /\
    (!e1 e2:ntp4vc_defun_expr.
       ntp4vc_defun_eval_expr (NTP4VCDefunSub e1 e2) =
       ntp4vc_defun_eval_expr e1 - ntp4vc_defun_eval_expr e2)`;;

let ntp4vc_defun_eval_cont_RULES,
    ntp4vc_defun_eval_cont_INDUCT,
    ntp4vc_defun_eval_cont_CASES =
  new_inductive_definition
   `(!v:int.
     !k:ntp4vc_defun_cont.
     !e2:ntp4vc_defun_expr.
     !r:int.
       ntp4vc_defun_eval_cont
         (NTP4VCDefunA2 v k) (ntp4vc_defun_eval_expr e2) r
       ==>
       ntp4vc_defun_eval_cont (NTP4VCDefunA1 e2 k) v r) /\
    (!k:ntp4vc_defun_cont.
     !v1 v r:int.
       ntp4vc_defun_eval_cont k (v1 - v) r
       ==>
       ntp4vc_defun_eval_cont (NTP4VCDefunA2 v1 k) v r) /\
    (!v:int. ntp4vc_defun_eval_cont NTP4VCDefunI v v)`;;

let ntp4vc_defun_size_expr =
  new_recursive_definition ntp4vc_defun_expr_RECURSION
   `(!n:int.
       ntp4vc_defun_size_expr (NTP4VCDefunCte n) = (&1:int)) /\
    (!e1 e2:ntp4vc_defun_expr.
       ntp4vc_defun_size_expr (NTP4VCDefunSub e1 e2) =
       (&3:int) + ntp4vc_defun_size_expr e1 +
       ntp4vc_defun_size_expr e2)`;;

let ntp4vc_defun_size_cont =
  new_recursive_definition ntp4vc_defun_cont_RECURSION
   `(ntp4vc_defun_size_cont NTP4VCDefunI = (&0:int)) /\
    (!e2:ntp4vc_defun_expr.
     !k:ntp4vc_defun_cont.
       ntp4vc_defun_size_cont (NTP4VCDefunA1 e2 k) =
       (&2:int) + ntp4vc_defun_size_expr e2 +
       ntp4vc_defun_size_cont k) /\
    (!x:int.
     !k:ntp4vc_defun_cont.
       ntp4vc_defun_size_cont (NTP4VCDefunA2 x k) =
       (&1:int) + ntp4vc_defun_size_cont k)`;;

let ntp4vc_defun_measure_case =
  new_recursive_definition ntp4vc_defun_cont_RECURSION
   `(!v:int.
       ntp4vc_defun_measure_case NTP4VCDefunI v = T) /\
    (!e2:ntp4vc_defun_expr.
     !k:ntp4vc_defun_cont.
     !v:int.
       ntp4vc_defun_measure_case (NTP4VCDefunA1 e2 k) v =
       ((&0:int) <= ntp4vc_defun_size_cont (NTP4VCDefunA1 e2 k) /\
        ntp4vc_defun_size_cont (NTP4VCDefunA2 v k) +
          ntp4vc_defun_size_expr e2 <
        ntp4vc_defun_size_cont (NTP4VCDefunA1 e2 k))) /\
    (!v1:int.
     !k:ntp4vc_defun_cont.
     !v:int.
       ntp4vc_defun_measure_case (NTP4VCDefunA2 v1 k) v =
       ((&0:int) <= ntp4vc_defun_size_cont (NTP4VCDefunA2 v1 k) /\
        ntp4vc_defun_size_cont k <
        ntp4vc_defun_size_cont (NTP4VCDefunA2 v1 k)))`;;

let ntp4vc_defun_step_case =
  new_recursive_definition ntp4vc_defun_cont_RECURSION
   `(!v result:int.
       ntp4vc_defun_step_case NTP4VCDefunI v result =
       (result = v)) /\
    (!e2:ntp4vc_defun_expr.
     !k:ntp4vc_defun_cont.
     !v result:int.
       ntp4vc_defun_step_case (NTP4VCDefunA1 e2 k) v result =
       ntp4vc_defun_eval_cont
         (NTP4VCDefunA2 v k) (ntp4vc_defun_eval_expr e2) result) /\
    (!v1:int.
     !k:ntp4vc_defun_cont.
     !v result:int.
       ntp4vc_defun_step_case (NTP4VCDefunA2 v1 k) v result =
       ntp4vc_defun_eval_cont k (v1 - v) result)`;;

let statement =
 `!c:ntp4vc_defun_cont.
  !v:int.
    ntp4vc_defun_measure_case c v /\
    (!result:int.
       ntp4vc_defun_step_case c v result
       ==> ntp4vc_defun_eval_cont c v result)`;;
