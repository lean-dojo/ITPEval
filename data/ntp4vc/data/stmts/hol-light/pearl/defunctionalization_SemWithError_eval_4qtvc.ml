(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/defunctionalization_SemWithError_eval_4qtvc: an underflow-aware
  defunctionalized expression-evaluation verification condition asserting
  structural measure decrease and preservation by continuation evaluation.
  This file contains no proof.
*)

let ntp4vc_swee4_expr_INDUCT,ntp4vc_swee4_expr_RECURSION = define_type
  "ntp4vc_swee4_expr =
       NTP4VC_SWEE4_Cte int
     | NTP4VC_SWEE4_Sub ntp4vc_swee4_expr ntp4vc_swee4_expr";;

let ntp4vc_swee4_value_INDUCT,ntp4vc_swee4_value_RECURSION = define_type
  "ntp4vc_swee4_value =
       NTP4VC_SWEE4_Vnum int
     | NTP4VC_SWEE4_Underflow";;

let ntp4vc_swee4_cont_INDUCT,ntp4vc_swee4_cont_RECURSION = define_type
  "ntp4vc_swee4_cont =
       NTP4VC_SWEE4_I
     | NTP4VC_SWEE4_A ntp4vc_swee4_expr ntp4vc_swee4_cont
     | NTP4VC_SWEE4_B int ntp4vc_swee4_cont";;

let ntp4vc_swee4_sub_from =
  new_recursive_definition ntp4vc_swee4_value_RECURSION
   `(!v1:int.
       ntp4vc_swee4_sub_from NTP4VC_SWEE4_Underflow v1 =
       NTP4VC_SWEE4_Underflow) /\
    (!v2 v1:int.
       ntp4vc_swee4_sub_from (NTP4VC_SWEE4_Vnum v2) v1 =
       (if v2 <= v1
        then NTP4VC_SWEE4_Vnum (v1 - v2)
        else NTP4VC_SWEE4_Underflow))`;;

let ntp4vc_swee4_sub_value =
  new_recursive_definition ntp4vc_swee4_value_RECURSION
   `(!v2:ntp4vc_swee4_value.
       ntp4vc_swee4_sub_value NTP4VC_SWEE4_Underflow v2 =
       NTP4VC_SWEE4_Underflow) /\
    (!v1:int.
     !v2:ntp4vc_swee4_value.
       ntp4vc_swee4_sub_value (NTP4VC_SWEE4_Vnum v1) v2 =
       ntp4vc_swee4_sub_from v2 v1)`;;

let ntp4vc_swee4_eval0 =
  new_recursive_definition ntp4vc_swee4_expr_RECURSION
   `(!n:int.
       ntp4vc_swee4_eval0 (NTP4VC_SWEE4_Cte n) =
       (if (&0:int) <= n
        then NTP4VC_SWEE4_Vnum n
        else NTP4VC_SWEE4_Underflow)) /\
    (!e1 e2:ntp4vc_swee4_expr.
       ntp4vc_swee4_eval0 (NTP4VC_SWEE4_Sub e1 e2) =
       ntp4vc_swee4_sub_value
         (ntp4vc_swee4_eval0 e1) (ntp4vc_swee4_eval0 e2))`;;

let ntp4vc_swee4_eval_cont_RULES,
    ntp4vc_swee4_eval_cont_INDUCT,
    ntp4vc_swee4_eval_cont_CASES =
  new_inductive_definition
   `(!k:ntp4vc_swee4_cont.
       ntp4vc_swee4_eval_cont
         k NTP4VC_SWEE4_Underflow NTP4VC_SWEE4_Underflow) /\
    (!v:int.
     !k:ntp4vc_swee4_cont.
     !e2:ntp4vc_swee4_expr.
     !r:ntp4vc_swee4_value.
       ntp4vc_swee4_eval_cont
         (NTP4VC_SWEE4_B v k) (ntp4vc_swee4_eval0 e2) r
       ==>
       ntp4vc_swee4_eval_cont
         (NTP4VC_SWEE4_A e2 k) (NTP4VC_SWEE4_Vnum v) r) /\
    (!k:ntp4vc_swee4_cont.
     !v v1:int.
     !r:ntp4vc_swee4_value.
       ntp4vc_swee4_eval_cont
         k
         (if v <= v1
          then NTP4VC_SWEE4_Vnum (v1 - v)
          else NTP4VC_SWEE4_Underflow)
         r
       ==>
       ntp4vc_swee4_eval_cont
         (NTP4VC_SWEE4_B v1 k) (NTP4VC_SWEE4_Vnum v) r) /\
    (!v:int.
       ntp4vc_swee4_eval_cont
         NTP4VC_SWEE4_I
         (NTP4VC_SWEE4_Vnum v)
         (NTP4VC_SWEE4_Vnum v))`;;

let ntp4vc_swee4_size_e =
  new_recursive_definition ntp4vc_swee4_expr_RECURSION
   `(!x:int.
       ntp4vc_swee4_size_e (NTP4VC_SWEE4_Cte x) = (&1:int)) /\
    (!e1 e2:ntp4vc_swee4_expr.
       ntp4vc_swee4_size_e (NTP4VC_SWEE4_Sub e1 e2) =
       (&3:int) + ntp4vc_swee4_size_e e1 + ntp4vc_swee4_size_e e2)`;;

let ntp4vc_swee4_size_c =
  new_recursive_definition ntp4vc_swee4_cont_RECURSION
   `(ntp4vc_swee4_size_c NTP4VC_SWEE4_I = (&0:int)) /\
    (!e2:ntp4vc_swee4_expr.
     !k:ntp4vc_swee4_cont.
       ntp4vc_swee4_size_c (NTP4VC_SWEE4_A e2 k) =
       (&2:int) + ntp4vc_swee4_size_e e2 +
       ntp4vc_swee4_size_c k) /\
    (!x:int.
     !k:ntp4vc_swee4_cont.
       ntp4vc_swee4_size_c (NTP4VC_SWEE4_B x k) =
       (&1:int) + ntp4vc_swee4_size_c k)`;;

let ntp4vc_swee4_measure_condition =
  new_recursive_definition ntp4vc_swee4_expr_RECURSION
   `(!n:int.
     !c:ntp4vc_swee4_cont.
       ntp4vc_swee4_measure_condition (NTP4VC_SWEE4_Cte n) c <=>
       ((&0:int) <= n
        ==>
        (((&0:int) <=
            ntp4vc_swee4_size_c c +
            ntp4vc_swee4_size_e (NTP4VC_SWEE4_Cte n) /\
          ntp4vc_swee4_size_c c <
            ntp4vc_swee4_size_c c +
            ntp4vc_swee4_size_e (NTP4VC_SWEE4_Cte n)) /\
         (&0:int) <= n))) /\
    (!e1 e2:ntp4vc_swee4_expr.
     !c:ntp4vc_swee4_cont.
       ntp4vc_swee4_measure_condition
         (NTP4VC_SWEE4_Sub e1 e2) c <=>
       ((&0:int) <=
          ntp4vc_swee4_size_c c +
          ntp4vc_swee4_size_e (NTP4VC_SWEE4_Sub e1 e2) /\
        ntp4vc_swee4_size_c (NTP4VC_SWEE4_A e2 c) +
          ntp4vc_swee4_size_e e1 <
        ntp4vc_swee4_size_c c +
          ntp4vc_swee4_size_e (NTP4VC_SWEE4_Sub e1 e2)))`;;

let ntp4vc_swee4_eval_premise =
  new_recursive_definition ntp4vc_swee4_expr_RECURSION
   `(!n:int.
     !c:ntp4vc_swee4_cont.
     !result:ntp4vc_swee4_value.
       ntp4vc_swee4_eval_premise
         (NTP4VC_SWEE4_Cte n) c result <=>
       (if (&0:int) <= n
        then ntp4vc_swee4_eval_cont
               c (NTP4VC_SWEE4_Vnum n) result
        else result = NTP4VC_SWEE4_Underflow)) /\
    (!e1 e2:ntp4vc_swee4_expr.
     !c:ntp4vc_swee4_cont.
     !result:ntp4vc_swee4_value.
       ntp4vc_swee4_eval_premise
         (NTP4VC_SWEE4_Sub e1 e2) c result <=>
       ntp4vc_swee4_eval_cont
         (NTP4VC_SWEE4_A e2 c) (ntp4vc_swee4_eval0 e1) result)`;;

let statement =
  `!e:ntp4vc_swee4_expr.
   !c:ntp4vc_swee4_cont.
     ntp4vc_swee4_measure_condition e c /\
     (!result:ntp4vc_swee4_value.
        ntp4vc_swee4_eval_premise e c result
        ==>
        ntp4vc_swee4_eval_cont c (ntp4vc_swee4_eval0 e) result)`;;
