(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/defunctionalization_RWithError_interpretqtvc: recomposition with the
  empty evaluation context preserves the underflow-aware interpretation of an
  integer subtraction expression. This file contains no proof.
*)

let ntp4vc_rwei_expr_INDUCT,ntp4vc_rwei_expr_RECURSION = define_type
  "ntp4vc_rwei_expr =
       NTP4VC_RWEI_Cte int
     | NTP4VC_RWEI_Sub ntp4vc_rwei_expr ntp4vc_rwei_expr";;

let ntp4vc_rwei_value_INDUCT,ntp4vc_rwei_value_RECURSION = define_type
  "ntp4vc_rwei_value =
       NTP4VC_RWEI_Vnum int
     | NTP4VC_RWEI_Underflow";;

let ntp4vc_rwei_context_INDUCT,ntp4vc_rwei_context_RECURSION = define_type
  "ntp4vc_rwei_context =
       NTP4VC_RWEI_Empty
     | NTP4VC_RWEI_Left ntp4vc_rwei_context ntp4vc_rwei_expr
     | NTP4VC_RWEI_Right int ntp4vc_rwei_context";;

let ntp4vc_rwei_size_e =
  new_recursive_definition ntp4vc_rwei_expr_RECURSION
   `(!n:int.
       ntp4vc_rwei_size_e (NTP4VC_RWEI_Cte n) = (&1:int)) /\
    (!e1 e2:ntp4vc_rwei_expr.
       ntp4vc_rwei_size_e (NTP4VC_RWEI_Sub e1 e2) =
       (&3:int) + ntp4vc_rwei_size_e e1 + ntp4vc_rwei_size_e e2)`;;

let ntp4vc_rwei_sub_from =
  new_recursive_definition ntp4vc_rwei_value_RECURSION
   `(!v1:int.
       ntp4vc_rwei_sub_from NTP4VC_RWEI_Underflow v1 =
       NTP4VC_RWEI_Underflow) /\
    (!v2 v1:int.
       ntp4vc_rwei_sub_from (NTP4VC_RWEI_Vnum v2) v1 =
       (if v2 <= v1
        then NTP4VC_RWEI_Vnum (v1 - v2)
        else NTP4VC_RWEI_Underflow))`;;

let ntp4vc_rwei_sub_value =
  new_recursive_definition ntp4vc_rwei_value_RECURSION
   `(!v2:ntp4vc_rwei_value.
       ntp4vc_rwei_sub_value NTP4VC_RWEI_Underflow v2 =
       NTP4VC_RWEI_Underflow) /\
    (!v1:int.
     !v2:ntp4vc_rwei_value.
       ntp4vc_rwei_sub_value (NTP4VC_RWEI_Vnum v1) v2 =
       ntp4vc_rwei_sub_from v2 v1)`;;

let ntp4vc_rwei_eval0 =
  new_recursive_definition ntp4vc_rwei_expr_RECURSION
   `(!n:int.
       ntp4vc_rwei_eval0 (NTP4VC_RWEI_Cte n) =
       (if (&0:int) <= n
        then NTP4VC_RWEI_Vnum n
        else NTP4VC_RWEI_Underflow)) /\
    (!e1 e2:ntp4vc_rwei_expr.
       ntp4vc_rwei_eval0 (NTP4VC_RWEI_Sub e1 e2) =
       ntp4vc_rwei_sub_value
         (ntp4vc_rwei_eval0 e1) (ntp4vc_rwei_eval0 e2))`;;

let ntp4vc_rwei_size_c =
  new_recursive_definition ntp4vc_rwei_context_RECURSION
   `(ntp4vc_rwei_size_c NTP4VC_RWEI_Empty = (&0:int)) /\
    (!c1:ntp4vc_rwei_context.
     !e:ntp4vc_rwei_expr.
       ntp4vc_rwei_size_c (NTP4VC_RWEI_Left c1 e) =
       (&2:int) + ntp4vc_rwei_size_c c1 + ntp4vc_rwei_size_e e) /\
    (!n:int.
     !c1:ntp4vc_rwei_context.
       ntp4vc_rwei_size_c (NTP4VC_RWEI_Right n c1) =
       (&1:int) + ntp4vc_rwei_size_c c1)`;;

let ntp4vc_rwei_recompose =
  new_recursive_definition ntp4vc_rwei_context_RECURSION
   `(!e:ntp4vc_rwei_expr.
       ntp4vc_rwei_recompose NTP4VC_RWEI_Empty e = e) /\
    (!c1:ntp4vc_rwei_context.
     !e2 e:ntp4vc_rwei_expr.
       ntp4vc_rwei_recompose (NTP4VC_RWEI_Left c1 e2) e =
       ntp4vc_rwei_recompose c1 (NTP4VC_RWEI_Sub e e2)) /\
    (!n1:int.
     !c1:ntp4vc_rwei_context.
     !e:ntp4vc_rwei_expr.
       ntp4vc_rwei_recompose (NTP4VC_RWEI_Right n1 c1) e =
       ntp4vc_rwei_recompose c1
         (NTP4VC_RWEI_Sub (NTP4VC_RWEI_Cte n1) e))`;;

let statement =
  `!p:ntp4vc_rwei_expr.
     ntp4vc_rwei_eval0 (ntp4vc_rwei_recompose NTP4VC_RWEI_Empty p) =
     ntp4vc_rwei_eval0 p`;;
