(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/defunctionalization_ReductionSemantics_itere_optqtvc: an iteration
  verification condition for reduction semantics, preserving direct integer
  evaluation under expression-context recomposition and identifying a final
  constant value in the empty context. This file contains no proof.
*)

let ntp4vc_rso_expr_INDUCT,ntp4vc_rso_expr_RECURSION = define_type
  "ntp4vc_rso_expr =
       NTP4VC_RSO_Cte int
     | NTP4VC_RSO_Sub ntp4vc_rso_expr ntp4vc_rso_expr";;

let ntp4vc_rso_context_INDUCT,ntp4vc_rso_context_RECURSION = define_type
  "ntp4vc_rso_context =
       NTP4VC_RSO_Empty
     | NTP4VC_RSO_Left ntp4vc_rso_context ntp4vc_rso_expr
     | NTP4VC_RSO_Right int ntp4vc_rso_context";;

let ntp4vc_rso_eval0 =
  new_recursive_definition ntp4vc_rso_expr_RECURSION
   `(!n:int.
       ntp4vc_rso_eval0 (NTP4VC_RSO_Cte n) = n) /\
    (!e1 e2:ntp4vc_rso_expr.
       ntp4vc_rso_eval0 (NTP4VC_RSO_Sub e1 e2) =
       ntp4vc_rso_eval0 e1 - ntp4vc_rso_eval0 e2)`;;

let ntp4vc_rso_is_value =
  new_recursive_definition ntp4vc_rso_expr_RECURSION
   `(!n:int.
       ntp4vc_rso_is_value (NTP4VC_RSO_Cte n) = T) /\
    (!e1 e2:ntp4vc_rso_expr.
       ntp4vc_rso_is_value (NTP4VC_RSO_Sub e1 e2) = F)`;;

let ntp4vc_rso_is_redex =
  new_recursive_definition ntp4vc_rso_expr_RECURSION
   `(!n:int.
       ntp4vc_rso_is_redex (NTP4VC_RSO_Cte n) = F) /\
    (!e1 e2:ntp4vc_rso_expr.
       ntp4vc_rso_is_redex (NTP4VC_RSO_Sub e1 e2) =
       (ntp4vc_rso_is_value e1 /\ ntp4vc_rso_is_value e2))`;;

let ntp4vc_rso_is_empty_context =
  new_recursive_definition ntp4vc_rso_context_RECURSION
   `(ntp4vc_rso_is_empty_context NTP4VC_RSO_Empty = T) /\
    (!c1:ntp4vc_rso_context.
     !e:ntp4vc_rso_expr.
       ntp4vc_rso_is_empty_context (NTP4VC_RSO_Left c1 e) = F) /\
    (!n:int.
     !c1:ntp4vc_rso_context.
       ntp4vc_rso_is_empty_context (NTP4VC_RSO_Right n c1) = F)`;;

let ntp4vc_rso_size_e =
  new_recursive_definition ntp4vc_rso_expr_RECURSION
   `(!n:int.
       ntp4vc_rso_size_e (NTP4VC_RSO_Cte n) = (&1:int)) /\
    (!e1 e2:ntp4vc_rso_expr.
       ntp4vc_rso_size_e (NTP4VC_RSO_Sub e1 e2) =
       (&3:int) + ntp4vc_rso_size_e e1 + ntp4vc_rso_size_e e2)`;;

let ntp4vc_rso_size_c =
  new_recursive_definition ntp4vc_rso_context_RECURSION
   `(ntp4vc_rso_size_c NTP4VC_RSO_Empty = (&0:int)) /\
    (!c1:ntp4vc_rso_context.
     !e:ntp4vc_rso_expr.
       ntp4vc_rso_size_c (NTP4VC_RSO_Left c1 e) =
       (&2:int) + ntp4vc_rso_size_c c1 + ntp4vc_rso_size_e e) /\
    (!n:int.
     !c1:ntp4vc_rso_context.
       ntp4vc_rso_size_c (NTP4VC_RSO_Right n c1) =
       (&1:int) + ntp4vc_rso_size_c c1)`;;

let ntp4vc_rso_recompose =
  new_recursive_definition ntp4vc_rso_context_RECURSION
   `(!e:ntp4vc_rso_expr.
       ntp4vc_rso_recompose NTP4VC_RSO_Empty e = e) /\
    (!c1:ntp4vc_rso_context.
     !e2 e:ntp4vc_rso_expr.
       ntp4vc_rso_recompose (NTP4VC_RSO_Left c1 e2) e =
       ntp4vc_rso_recompose c1 (NTP4VC_RSO_Sub e e2)) /\
    (!n1:int.
     !c1:ntp4vc_rso_context.
     !e:ntp4vc_rso_expr.
       ntp4vc_rso_recompose (NTP4VC_RSO_Right n1 c1) e =
       ntp4vc_rso_recompose c1
         (NTP4VC_RSO_Sub (NTP4VC_RSO_Cte n1) e))`;;

let ntp4vc_rso_constant_case =
  new_recursive_definition ntp4vc_rso_expr_RECURSION
   `(!n:int.
       ntp4vc_rso_constant_case (NTP4VC_RSO_Cte n) = T) /\
    (!e1 e2:ntp4vc_rso_expr.
       ntp4vc_rso_constant_case (NTP4VC_RSO_Sub e1 e2) = F)`;;

let ntp4vc_rso_result_case =
  new_recursive_definition ntp4vc_rso_expr_RECURSION
   `(!n result:int.
       ntp4vc_rso_result_case (NTP4VC_RSO_Cte n) result =
       (result = n)) /\
    (!e1 e2:ntp4vc_rso_expr.
     !result:int.
       ntp4vc_rso_result_case (NTP4VC_RSO_Sub e1 e2) result = F)`;;

let statement =
  `!c1:ntp4vc_rso_context.
   !e:ntp4vc_rso_expr.
     (!c:ntp4vc_rso_context.
      !r:ntp4vc_rso_expr.
        ntp4vc_rso_recompose c r = ntp4vc_rso_recompose c1 e /\
        ntp4vc_rso_is_redex r
        ==>
        ntp4vc_rso_is_redex r /\
        (!o1:ntp4vc_rso_expr.
           ntp4vc_rso_eval0 o1 = ntp4vc_rso_eval0 r
           ==>
           ntp4vc_rso_eval0 (ntp4vc_rso_recompose c o1) =
           ntp4vc_rso_eval0 (ntp4vc_rso_recompose c1 e))) /\
     (ntp4vc_rso_is_empty_context c1 /\ ntp4vc_rso_is_value e
      ==>
      ntp4vc_rso_constant_case e /\
      (!result:int.
         ntp4vc_rso_result_case e result
         ==>
         result = ntp4vc_rso_eval0 (ntp4vc_rso_recompose c1 e)))`;;
