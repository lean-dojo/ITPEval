(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/defunctionalization_SemWithError_continue_4qtvc: an underflow-aware
  defunctionalized continuation-step verification condition relating
  structural size decrease to continuation evaluation. This file contains
  no proof.
*)

let ntp4vc_swec4_expr_INDUCT,ntp4vc_swec4_expr_RECURSION = define_type
  "ntp4vc_swec4_expr =
       NTP4VC_SWEC4_Cte int
     | NTP4VC_SWEC4_Sub ntp4vc_swec4_expr ntp4vc_swec4_expr";;

let ntp4vc_swec4_value_INDUCT,ntp4vc_swec4_value_RECURSION = define_type
  "ntp4vc_swec4_value =
       NTP4VC_SWEC4_Vnum int
     | NTP4VC_SWEC4_Underflow";;

let ntp4vc_swec4_cont_INDUCT,ntp4vc_swec4_cont_RECURSION = define_type
  "ntp4vc_swec4_cont =
       NTP4VC_SWEC4_I
     | NTP4VC_SWEC4_A ntp4vc_swec4_expr ntp4vc_swec4_cont
     | NTP4VC_SWEC4_B int ntp4vc_swec4_cont";;

let ntp4vc_swec4_sub_from =
  new_recursive_definition ntp4vc_swec4_value_RECURSION
   `(!v1:int.
       ntp4vc_swec4_sub_from NTP4VC_SWEC4_Underflow v1 =
       NTP4VC_SWEC4_Underflow) /\
    (!v2 v1:int.
       ntp4vc_swec4_sub_from (NTP4VC_SWEC4_Vnum v2) v1 =
       (if v2 <= v1
        then NTP4VC_SWEC4_Vnum (v1 - v2)
        else NTP4VC_SWEC4_Underflow))`;;

let ntp4vc_swec4_sub_value =
  new_recursive_definition ntp4vc_swec4_value_RECURSION
   `(!v2:ntp4vc_swec4_value.
       ntp4vc_swec4_sub_value NTP4VC_SWEC4_Underflow v2 =
       NTP4VC_SWEC4_Underflow) /\
    (!v1:int.
     !v2:ntp4vc_swec4_value.
       ntp4vc_swec4_sub_value (NTP4VC_SWEC4_Vnum v1) v2 =
       ntp4vc_swec4_sub_from v2 v1)`;;

let ntp4vc_swec4_eval0 =
  new_recursive_definition ntp4vc_swec4_expr_RECURSION
   `(!n:int.
       ntp4vc_swec4_eval0 (NTP4VC_SWEC4_Cte n) =
       (if (&0:int) <= n
        then NTP4VC_SWEC4_Vnum n
        else NTP4VC_SWEC4_Underflow)) /\
    (!e1 e2:ntp4vc_swec4_expr.
       ntp4vc_swec4_eval0 (NTP4VC_SWEC4_Sub e1 e2) =
       ntp4vc_swec4_sub_value
         (ntp4vc_swec4_eval0 e1) (ntp4vc_swec4_eval0 e2))`;;

let ntp4vc_swec4_eval_cont_RULES,
    ntp4vc_swec4_eval_cont_INDUCT,
    ntp4vc_swec4_eval_cont_CASES =
  new_inductive_definition
   `(!k:ntp4vc_swec4_cont.
       ntp4vc_swec4_eval_cont
         k NTP4VC_SWEC4_Underflow NTP4VC_SWEC4_Underflow) /\
    (!v:int.
     !k:ntp4vc_swec4_cont.
     !e2:ntp4vc_swec4_expr.
     !r:ntp4vc_swec4_value.
       ntp4vc_swec4_eval_cont
         (NTP4VC_SWEC4_B v k) (ntp4vc_swec4_eval0 e2) r
       ==>
       ntp4vc_swec4_eval_cont
         (NTP4VC_SWEC4_A e2 k) (NTP4VC_SWEC4_Vnum v) r) /\
    (!k:ntp4vc_swec4_cont.
     !v v1:int.
     !r:ntp4vc_swec4_value.
       ntp4vc_swec4_eval_cont
         k
         (if v <= v1
          then NTP4VC_SWEC4_Vnum (v1 - v)
          else NTP4VC_SWEC4_Underflow)
         r
       ==>
       ntp4vc_swec4_eval_cont
         (NTP4VC_SWEC4_B v1 k) (NTP4VC_SWEC4_Vnum v) r) /\
    (!v:int.
       ntp4vc_swec4_eval_cont
         NTP4VC_SWEC4_I
         (NTP4VC_SWEC4_Vnum v)
         (NTP4VC_SWEC4_Vnum v))`;;

let ntp4vc_swec4_size_e =
  new_recursive_definition ntp4vc_swec4_expr_RECURSION
   `(!x:int.
       ntp4vc_swec4_size_e (NTP4VC_SWEC4_Cte x) = (&1:int)) /\
    (!e1 e2:ntp4vc_swec4_expr.
       ntp4vc_swec4_size_e (NTP4VC_SWEC4_Sub e1 e2) =
       (&3:int) + ntp4vc_swec4_size_e e1 + ntp4vc_swec4_size_e e2)`;;

let ntp4vc_swec4_size_c =
  new_recursive_definition ntp4vc_swec4_cont_RECURSION
   `(ntp4vc_swec4_size_c NTP4VC_SWEC4_I = (&0:int)) /\
    (!e2:ntp4vc_swec4_expr.
     !k:ntp4vc_swec4_cont.
       ntp4vc_swec4_size_c (NTP4VC_SWEC4_A e2 k) =
       (&2:int) + ntp4vc_swec4_size_e e2 +
       ntp4vc_swec4_size_c k) /\
    (!x:int.
     !k:ntp4vc_swec4_cont.
       ntp4vc_swec4_size_c (NTP4VC_SWEC4_B x k) =
       (&1:int) + ntp4vc_swec4_size_c k)`;;

let ntp4vc_swec4_measure_case =
  new_recursive_definition ntp4vc_swec4_cont_RECURSION
   `(!v:int.
       ntp4vc_swec4_measure_case NTP4VC_SWEC4_I v = T) /\
    (!e2:ntp4vc_swec4_expr.
     !k:ntp4vc_swec4_cont.
     !v:int.
       ntp4vc_swec4_measure_case (NTP4VC_SWEC4_A e2 k) v =
       ((&0:int) <=
          ntp4vc_swec4_size_c (NTP4VC_SWEC4_A e2 k) /\
        ntp4vc_swec4_size_c (NTP4VC_SWEC4_B v k) +
          ntp4vc_swec4_size_e e2 <
        ntp4vc_swec4_size_c (NTP4VC_SWEC4_A e2 k))) /\
    (!v1:int.
     !k:ntp4vc_swec4_cont.
     !v:int.
       ntp4vc_swec4_measure_case (NTP4VC_SWEC4_B v1 k) v =
       (v <= v1
        ==>
        (((&0:int) <=
            ntp4vc_swec4_size_c (NTP4VC_SWEC4_B v1 k) /\
          ntp4vc_swec4_size_c k <
            ntp4vc_swec4_size_c (NTP4VC_SWEC4_B v1 k)) /\
         (&0:int) <= v1 - v)))`;;

let ntp4vc_swec4_step_case =
  new_recursive_definition ntp4vc_swec4_cont_RECURSION
   `(!v:int.
     !result:ntp4vc_swec4_value.
       ntp4vc_swec4_step_case NTP4VC_SWEC4_I v result =
       (result = NTP4VC_SWEC4_Vnum v)) /\
    (!e2:ntp4vc_swec4_expr.
     !k:ntp4vc_swec4_cont.
     !v:int.
     !result:ntp4vc_swec4_value.
       ntp4vc_swec4_step_case
         (NTP4VC_SWEC4_A e2 k) v result =
       ntp4vc_swec4_eval_cont
         (NTP4VC_SWEC4_B v k) (ntp4vc_swec4_eval0 e2) result) /\
    (!v1:int.
     !k:ntp4vc_swec4_cont.
     !v:int.
     !result:ntp4vc_swec4_value.
       ntp4vc_swec4_step_case
         (NTP4VC_SWEC4_B v1 k) v result =
       (if v <= v1
        then ntp4vc_swec4_eval_cont
               k (NTP4VC_SWEC4_Vnum (v1 - v)) result
        else result = NTP4VC_SWEC4_Underflow))`;;

let statement =
  `!v:int.
   !c:ntp4vc_swec4_cont.
     (&0:int) <= v
     ==>
     ntp4vc_swec4_measure_case c v /\
     (!result:ntp4vc_swec4_value.
        ntp4vc_swec4_step_case c v result
        ==>
        ntp4vc_swec4_eval_cont c (NTP4VC_SWEC4_Vnum v) result)`;;
