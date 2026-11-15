(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/defunctionalization_Defunctionalization_eval_2qtvc:
  a defunctionalized expression-evaluation verification condition stating
  structural measure decrease and preservation of direct integer evaluation
  by continuation evaluation. This file contains no proof.
*)

let ntp4vc_defun_expr_INDUCT,ntp4vc_defun_expr_RECURSION = define_type
  "ntp4vc_defun_expr =
       NTP4VC_Defun_Cte int
     | NTP4VC_Defun_Sub ntp4vc_defun_expr ntp4vc_defun_expr";;

let ntp4vc_defun_cont_INDUCT,ntp4vc_defun_cont_RECURSION = define_type
  "ntp4vc_defun_cont =
       NTP4VC_Defun_A1 ntp4vc_defun_expr ntp4vc_defun_cont
     | NTP4VC_Defun_A2 int ntp4vc_defun_cont
     | NTP4VC_Defun_I";;

let ntp4vc_defun_eval0 =
  new_recursive_definition ntp4vc_defun_expr_RECURSION
   `(!n:int.
       ntp4vc_defun_eval0 (NTP4VC_Defun_Cte n) = n) /\
    (!e1 e2:ntp4vc_defun_expr.
       ntp4vc_defun_eval0 (NTP4VC_Defun_Sub e1 e2) =
       ntp4vc_defun_eval0 e1 - ntp4vc_defun_eval0 e2)`;;

let ntp4vc_defun_eval_cont_RULES,
    ntp4vc_defun_eval_cont_INDUCT,
    ntp4vc_defun_eval_cont_CASES =
  new_inductive_definition
   `(!v:int.
     !k:ntp4vc_defun_cont.
     !e2:ntp4vc_defun_expr.
     !r:int.
       ntp4vc_defun_eval_cont
         (NTP4VC_Defun_A2 v k) (ntp4vc_defun_eval0 e2) r
       ==> ntp4vc_defun_eval_cont (NTP4VC_Defun_A1 e2 k) v r) /\
    (!k:ntp4vc_defun_cont.
     !v1 v r:int.
       ntp4vc_defun_eval_cont k (v1 - v) r
       ==> ntp4vc_defun_eval_cont (NTP4VC_Defun_A2 v1 k) v r) /\
    (!v:int.
       ntp4vc_defun_eval_cont NTP4VC_Defun_I v v)`;;

let ntp4vc_defun_size_e =
  new_recursive_definition ntp4vc_defun_expr_RECURSION
   `(!n:int.
       ntp4vc_defun_size_e (NTP4VC_Defun_Cte n) = (&1:int)) /\
    (!e1 e2:ntp4vc_defun_expr.
       ntp4vc_defun_size_e (NTP4VC_Defun_Sub e1 e2) =
       (&3:int) + ntp4vc_defun_size_e e1 + ntp4vc_defun_size_e e2)`;;

let ntp4vc_defun_size_c =
  new_recursive_definition ntp4vc_defun_cont_RECURSION
   `(ntp4vc_defun_size_c NTP4VC_Defun_I = (&0:int)) /\
    (!e2:ntp4vc_defun_expr.
     !k:ntp4vc_defun_cont.
       ntp4vc_defun_size_c (NTP4VC_Defun_A1 e2 k) =
       (&2:int) + ntp4vc_defun_size_e e2 + ntp4vc_defun_size_c k) /\
    (!v:int.
     !k:ntp4vc_defun_cont.
       ntp4vc_defun_size_c (NTP4VC_Defun_A2 v k) =
       (&1:int) + ntp4vc_defun_size_c k)`;;

let ntp4vc_defun_measure_condition =
  new_recursive_definition ntp4vc_defun_expr_RECURSION
   `(!n:int.
     !c:ntp4vc_defun_cont.
       ntp4vc_defun_measure_condition (NTP4VC_Defun_Cte n) c <=>
       (&0:int) <=
         ntp4vc_defun_size_c c +
         ntp4vc_defun_size_e (NTP4VC_Defun_Cte n) /\
       ntp4vc_defun_size_c c <
         ntp4vc_defun_size_c c +
         ntp4vc_defun_size_e (NTP4VC_Defun_Cte n)) /\
    (!e1 e2:ntp4vc_defun_expr.
     !c:ntp4vc_defun_cont.
       ntp4vc_defun_measure_condition (NTP4VC_Defun_Sub e1 e2) c <=>
       (&0:int) <=
         ntp4vc_defun_size_c c +
         ntp4vc_defun_size_e (NTP4VC_Defun_Sub e1 e2) /\
       ntp4vc_defun_size_c (NTP4VC_Defun_A1 e2 c) +
         ntp4vc_defun_size_e e1 <
       ntp4vc_defun_size_c c +
         ntp4vc_defun_size_e (NTP4VC_Defun_Sub e1 e2))`;;

let ntp4vc_defun_eval_premise =
  new_recursive_definition ntp4vc_defun_expr_RECURSION
   `(!n:int.
     !c:ntp4vc_defun_cont.
     !result:int.
       ntp4vc_defun_eval_premise
         (NTP4VC_Defun_Cte n) c result <=>
       ntp4vc_defun_eval_cont c n result) /\
    (!e1 e2:ntp4vc_defun_expr.
     !c:ntp4vc_defun_cont.
     !result:int.
       ntp4vc_defun_eval_premise
         (NTP4VC_Defun_Sub e1 e2) c result <=>
       ntp4vc_defun_eval_cont
         (NTP4VC_Defun_A1 e2 c) (ntp4vc_defun_eval0 e1) result)`;;

let statement =
  `!e:ntp4vc_defun_expr.
   !c:ntp4vc_defun_cont.
     ntp4vc_defun_measure_condition e c /\
     (!result:int.
        ntp4vc_defun_eval_premise e c result
        ==> ntp4vc_defun_eval_cont c (ntp4vc_defun_eval0 e) result)`;;
