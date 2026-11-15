(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/defunctionalization_RWithError_eval_1qtvc: an underflow-aware
  defunctionalized expression-evaluation verification condition stating
  structural measure decrease and preservation of the recomposed expression's
  error-aware value. This file contains no proof.
*)

let ntp4vc_rwe_expr_INDUCT,ntp4vc_rwe_expr_RECURSION = define_type
  "ntp4vc_rwe_expr =
       NTP4VC_RWE_Cte int
     | NTP4VC_RWE_Sub ntp4vc_rwe_expr ntp4vc_rwe_expr";;

let ntp4vc_rwe_value_INDUCT,ntp4vc_rwe_value_RECURSION = define_type
  "ntp4vc_rwe_value =
       NTP4VC_RWE_Vnum int
     | NTP4VC_RWE_Underflow";;

let ntp4vc_rwe_context_INDUCT,ntp4vc_rwe_context_RECURSION = define_type
  "ntp4vc_rwe_context =
       NTP4VC_RWE_Empty
     | NTP4VC_RWE_Left ntp4vc_rwe_context ntp4vc_rwe_expr
     | NTP4VC_RWE_Right int ntp4vc_rwe_context";;

let ntp4vc_rwe_size_e =
  new_recursive_definition ntp4vc_rwe_expr_RECURSION
   `(!n:int.
       ntp4vc_rwe_size_e (NTP4VC_RWE_Cte n) = (&1:int)) /\
    (!e1 e2:ntp4vc_rwe_expr.
       ntp4vc_rwe_size_e (NTP4VC_RWE_Sub e1 e2) =
       (&3:int) + ntp4vc_rwe_size_e e1 + ntp4vc_rwe_size_e e2)`;;

let ntp4vc_rwe_sub_from =
  new_recursive_definition ntp4vc_rwe_value_RECURSION
   `(!v1:int.
       ntp4vc_rwe_sub_from NTP4VC_RWE_Underflow v1 =
       NTP4VC_RWE_Underflow) /\
    (!v2 v1:int.
       ntp4vc_rwe_sub_from (NTP4VC_RWE_Vnum v2) v1 =
       (if v2 <= v1
        then NTP4VC_RWE_Vnum (v1 - v2)
        else NTP4VC_RWE_Underflow))`;;

let ntp4vc_rwe_sub_value =
  new_recursive_definition ntp4vc_rwe_value_RECURSION
   `(!v2:ntp4vc_rwe_value.
       ntp4vc_rwe_sub_value NTP4VC_RWE_Underflow v2 =
       NTP4VC_RWE_Underflow) /\
    (!v1:int.
     !v2:ntp4vc_rwe_value.
       ntp4vc_rwe_sub_value (NTP4VC_RWE_Vnum v1) v2 =
       ntp4vc_rwe_sub_from v2 v1)`;;

let ntp4vc_rwe_eval0 =
  new_recursive_definition ntp4vc_rwe_expr_RECURSION
   `(!n:int.
       ntp4vc_rwe_eval0 (NTP4VC_RWE_Cte n) =
       (if (&0:int) <= n
        then NTP4VC_RWE_Vnum n
        else NTP4VC_RWE_Underflow)) /\
    (!e1 e2:ntp4vc_rwe_expr.
       ntp4vc_rwe_eval0 (NTP4VC_RWE_Sub e1 e2) =
       ntp4vc_rwe_sub_value
         (ntp4vc_rwe_eval0 e1) (ntp4vc_rwe_eval0 e2))`;;

let ntp4vc_rwe_size_c =
  new_recursive_definition ntp4vc_rwe_context_RECURSION
   `(ntp4vc_rwe_size_c NTP4VC_RWE_Empty = (&0:int)) /\
    (!c1:ntp4vc_rwe_context.
     !e:ntp4vc_rwe_expr.
       ntp4vc_rwe_size_c (NTP4VC_RWE_Left c1 e) =
       (&2:int) + ntp4vc_rwe_size_c c1 + ntp4vc_rwe_size_e e) /\
    (!n:int.
     !c1:ntp4vc_rwe_context.
       ntp4vc_rwe_size_c (NTP4VC_RWE_Right n c1) =
       (&1:int) + ntp4vc_rwe_size_c c1)`;;

let ntp4vc_rwe_recompose =
  new_recursive_definition ntp4vc_rwe_context_RECURSION
   `(!e:ntp4vc_rwe_expr.
       ntp4vc_rwe_recompose NTP4VC_RWE_Empty e = e) /\
    (!c1:ntp4vc_rwe_context.
     !e2 e:ntp4vc_rwe_expr.
       ntp4vc_rwe_recompose (NTP4VC_RWE_Left c1 e2) e =
       ntp4vc_rwe_recompose c1 (NTP4VC_RWE_Sub e e2)) /\
    (!n1:int.
     !c1:ntp4vc_rwe_context.
     !e:ntp4vc_rwe_expr.
       ntp4vc_rwe_recompose (NTP4VC_RWE_Right n1 c1) e =
       ntp4vc_rwe_recompose c1
         (NTP4VC_RWE_Sub (NTP4VC_RWE_Cte n1) e))`;;

let ntp4vc_rwe_measure_condition =
  new_recursive_definition ntp4vc_rwe_expr_RECURSION
   `(!n:int.
     !c:ntp4vc_rwe_context.
       ntp4vc_rwe_measure_condition (NTP4VC_RWE_Cte n) c <=>
       ((&0:int) <= n
        ==>
        (((&0:int) <=
            (&2:int) *
              (ntp4vc_rwe_size_c c +
               ntp4vc_rwe_size_e (NTP4VC_RWE_Cte n)) /\
          (&1:int) + (&2:int) * ntp4vc_rwe_size_c c <
            (&2:int) *
              (ntp4vc_rwe_size_c c +
               ntp4vc_rwe_size_e (NTP4VC_RWE_Cte n))) /\
         (&0:int) <= n))) /\
    (!e1 e2:ntp4vc_rwe_expr.
     !c:ntp4vc_rwe_context.
       ntp4vc_rwe_measure_condition (NTP4VC_RWE_Sub e1 e2) c <=>
       ((&0:int) <=
          (&2:int) *
            (ntp4vc_rwe_size_c c +
             ntp4vc_rwe_size_e (NTP4VC_RWE_Sub e1 e2)) /\
        (&2:int) *
            (ntp4vc_rwe_size_c (NTP4VC_RWE_Left c e2) +
             ntp4vc_rwe_size_e e1) <
          (&2:int) *
            (ntp4vc_rwe_size_c c +
             ntp4vc_rwe_size_e (NTP4VC_RWE_Sub e1 e2))))`;;

let ntp4vc_rwe_eval_premise =
  new_recursive_definition ntp4vc_rwe_expr_RECURSION
   `(!n:int.
     !c:ntp4vc_rwe_context.
     !result:ntp4vc_rwe_value.
       ntp4vc_rwe_eval_premise (NTP4VC_RWE_Cte n) c result <=>
       (if (&0:int) <= n
        then result =
             ntp4vc_rwe_eval0
               (ntp4vc_rwe_recompose c (NTP4VC_RWE_Cte n))
        else result = NTP4VC_RWE_Underflow)) /\
    (!e1 e2:ntp4vc_rwe_expr.
     !c:ntp4vc_rwe_context.
     !result:ntp4vc_rwe_value.
       ntp4vc_rwe_eval_premise
         (NTP4VC_RWE_Sub e1 e2) c result <=>
       result =
         ntp4vc_rwe_eval0
           (ntp4vc_rwe_recompose (NTP4VC_RWE_Left c e2) e1))`;;

let statement =
  `!e:ntp4vc_rwe_expr.
   !c:ntp4vc_rwe_context.
     ntp4vc_rwe_measure_condition e c /\
     (!result:ntp4vc_rwe_value.
        ntp4vc_rwe_eval_premise e c result
        ==>
        result = ntp4vc_rwe_eval0 (ntp4vc_rwe_recompose c e))`;;
