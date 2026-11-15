(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/defunctionalization_ReductionSemantics_interpretqtvc: recomposition
  with the empty reduction-semantics context preserves direct integer
  evaluation of a subtraction expression. This file contains no proof.
*)

let ntp4vc_rsi_expr_INDUCT,ntp4vc_rsi_expr_RECURSION = define_type
  "ntp4vc_rsi_expr =
       NTP4VC_RSI_Cte int
     | NTP4VC_RSI_Sub ntp4vc_rsi_expr ntp4vc_rsi_expr";;

let ntp4vc_rsi_context_INDUCT,ntp4vc_rsi_context_RECURSION = define_type
  "ntp4vc_rsi_context =
       NTP4VC_RSI_Empty
     | NTP4VC_RSI_Left ntp4vc_rsi_context ntp4vc_rsi_expr
     | NTP4VC_RSI_Right int ntp4vc_rsi_context";;

let ntp4vc_rsi_eval0 =
  new_recursive_definition ntp4vc_rsi_expr_RECURSION
   `(!n:int.
       ntp4vc_rsi_eval0 (NTP4VC_RSI_Cte n) = n) /\
    (!e1 e2:ntp4vc_rsi_expr.
       ntp4vc_rsi_eval0 (NTP4VC_RSI_Sub e1 e2) =
       ntp4vc_rsi_eval0 e1 - ntp4vc_rsi_eval0 e2)`;;

let ntp4vc_rsi_is_redex =
  new_recursive_definition ntp4vc_rsi_expr_RECURSION
   `(!n:int.
       ntp4vc_rsi_is_redex (NTP4VC_RSI_Cte n) = F) /\
    (!e1 e2:ntp4vc_rsi_expr.
       ntp4vc_rsi_is_redex (NTP4VC_RSI_Sub e1 e2) =
       ((?n1:int. e1 = NTP4VC_RSI_Cte n1) /\
        (?n2:int. e2 = NTP4VC_RSI_Cte n2)))`;;

let ntp4vc_rsi_is_value =
  new_recursive_definition ntp4vc_rsi_expr_RECURSION
   `(!n:int.
       ntp4vc_rsi_is_value (NTP4VC_RSI_Cte n) = T) /\
    (!e1 e2:ntp4vc_rsi_expr.
       ntp4vc_rsi_is_value (NTP4VC_RSI_Sub e1 e2) = F)`;;

let ntp4vc_rsi_is_empty_context =
  new_recursive_definition ntp4vc_rsi_context_RECURSION
   `(ntp4vc_rsi_is_empty_context NTP4VC_RSI_Empty = T) /\
    (!c1:ntp4vc_rsi_context.
     !e:ntp4vc_rsi_expr.
       ntp4vc_rsi_is_empty_context (NTP4VC_RSI_Left c1 e) = F) /\
    (!n:int.
     !c1:ntp4vc_rsi_context.
       ntp4vc_rsi_is_empty_context (NTP4VC_RSI_Right n c1) = F)`;;

let ntp4vc_rsi_size_e =
  new_recursive_definition ntp4vc_rsi_expr_RECURSION
   `(!n:int.
       ntp4vc_rsi_size_e (NTP4VC_RSI_Cte n) = (&1:int)) /\
    (!e1 e2:ntp4vc_rsi_expr.
       ntp4vc_rsi_size_e (NTP4VC_RSI_Sub e1 e2) =
       (&3:int) + ntp4vc_rsi_size_e e1 + ntp4vc_rsi_size_e e2)`;;

let ntp4vc_rsi_size_c =
  new_recursive_definition ntp4vc_rsi_context_RECURSION
   `(ntp4vc_rsi_size_c NTP4VC_RSI_Empty = (&0:int)) /\
    (!c1:ntp4vc_rsi_context.
     !e:ntp4vc_rsi_expr.
       ntp4vc_rsi_size_c (NTP4VC_RSI_Left c1 e) =
       (&2:int) + ntp4vc_rsi_size_c c1 + ntp4vc_rsi_size_e e) /\
    (!n:int.
     !c1:ntp4vc_rsi_context.
       ntp4vc_rsi_size_c (NTP4VC_RSI_Right n c1) =
       (&1:int) + ntp4vc_rsi_size_c c1)`;;

let ntp4vc_rsi_recompose =
  new_recursive_definition ntp4vc_rsi_context_RECURSION
   `(!e:ntp4vc_rsi_expr.
       ntp4vc_rsi_recompose NTP4VC_RSI_Empty e = e) /\
    (!c1:ntp4vc_rsi_context.
     !e2 e:ntp4vc_rsi_expr.
       ntp4vc_rsi_recompose (NTP4VC_RSI_Left c1 e2) e =
       ntp4vc_rsi_recompose c1 (NTP4VC_RSI_Sub e e2)) /\
    (!n1:int.
     !c1:ntp4vc_rsi_context.
     !e:ntp4vc_rsi_expr.
       ntp4vc_rsi_recompose (NTP4VC_RSI_Right n1 c1) e =
       ntp4vc_rsi_recompose c1
         (NTP4VC_RSI_Sub (NTP4VC_RSI_Cte n1) e))`;;

let statement =
  `!p:ntp4vc_rsi_expr.
     ntp4vc_rsi_eval0 (ntp4vc_rsi_recompose NTP4VC_RSI_Empty p) =
     ntp4vc_rsi_eval0 p`;;
