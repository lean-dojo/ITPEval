(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/defunctionalization_ReductionSemantics_eval_1qtvc: a
  reduction-semantics verification condition stating structural measure
  decrease and preservation of direct integer evaluation when an arithmetic
  expression is decomposed under a context. This file contains no proof.
*)

let ntp4vc_rse_expr_INDUCT,ntp4vc_rse_expr_RECURSION = define_type
  "ntp4vc_rse_expr =
       NTP4VC_RSE_Cte int
     | NTP4VC_RSE_Sub ntp4vc_rse_expr ntp4vc_rse_expr";;

let ntp4vc_rse_context_INDUCT,ntp4vc_rse_context_RECURSION = define_type
  "ntp4vc_rse_context =
       NTP4VC_RSE_Empty
     | NTP4VC_RSE_Left ntp4vc_rse_context ntp4vc_rse_expr
     | NTP4VC_RSE_Right int ntp4vc_rse_context";;

let ntp4vc_rse_eval0 =
  new_recursive_definition ntp4vc_rse_expr_RECURSION
   `(!n:int.
       ntp4vc_rse_eval0 (NTP4VC_RSE_Cte n) = n) /\
    (!e1 e2:ntp4vc_rse_expr.
       ntp4vc_rse_eval0 (NTP4VC_RSE_Sub e1 e2) =
       ntp4vc_rse_eval0 e1 - ntp4vc_rse_eval0 e2)`;;

let ntp4vc_rse_size_e =
  new_recursive_definition ntp4vc_rse_expr_RECURSION
   `(!n:int.
       ntp4vc_rse_size_e (NTP4VC_RSE_Cte n) = (&1:int)) /\
    (!e1 e2:ntp4vc_rse_expr.
       ntp4vc_rse_size_e (NTP4VC_RSE_Sub e1 e2) =
       (&3:int) + ntp4vc_rse_size_e e1 + ntp4vc_rse_size_e e2)`;;

let ntp4vc_rse_size_c =
  new_recursive_definition ntp4vc_rse_context_RECURSION
   `(ntp4vc_rse_size_c NTP4VC_RSE_Empty = (&0:int)) /\
    (!c1:ntp4vc_rse_context.
     !e:ntp4vc_rse_expr.
       ntp4vc_rse_size_c (NTP4VC_RSE_Left c1 e) =
       (&2:int) + ntp4vc_rse_size_c c1 + ntp4vc_rse_size_e e) /\
    (!n:int.
     !c1:ntp4vc_rse_context.
       ntp4vc_rse_size_c (NTP4VC_RSE_Right n c1) =
       (&1:int) + ntp4vc_rse_size_c c1)`;;

let ntp4vc_rse_recompose =
  new_recursive_definition ntp4vc_rse_context_RECURSION
   `(!e:ntp4vc_rse_expr.
       ntp4vc_rse_recompose NTP4VC_RSE_Empty e = e) /\
    (!c1:ntp4vc_rse_context.
     !e2 e:ntp4vc_rse_expr.
       ntp4vc_rse_recompose (NTP4VC_RSE_Left c1 e2) e =
       ntp4vc_rse_recompose c1 (NTP4VC_RSE_Sub e e2)) /\
    (!n1:int.
     !c1:ntp4vc_rse_context.
     !e:ntp4vc_rse_expr.
       ntp4vc_rse_recompose (NTP4VC_RSE_Right n1 c1) e =
       ntp4vc_rse_recompose c1
         (NTP4VC_RSE_Sub (NTP4VC_RSE_Cte n1) e))`;;

let ntp4vc_rse_measure_condition =
  new_recursive_definition ntp4vc_rse_expr_RECURSION
   `(!n:int.
     !c:ntp4vc_rse_context.
       ntp4vc_rse_measure_condition (NTP4VC_RSE_Cte n) c <=>
       ((&0:int) <=
          (&2:int) *
            (ntp4vc_rse_size_c c +
             ntp4vc_rse_size_e (NTP4VC_RSE_Cte n)) /\
        (&1:int) + (&2:int) * ntp4vc_rse_size_c c <
          (&2:int) *
            (ntp4vc_rse_size_c c +
             ntp4vc_rse_size_e (NTP4VC_RSE_Cte n)))) /\
    (!e1 e2:ntp4vc_rse_expr.
     !c:ntp4vc_rse_context.
       ntp4vc_rse_measure_condition (NTP4VC_RSE_Sub e1 e2) c <=>
       ((&0:int) <=
          (&2:int) *
            (ntp4vc_rse_size_c c +
             ntp4vc_rse_size_e (NTP4VC_RSE_Sub e1 e2)) /\
        (&2:int) *
            (ntp4vc_rse_size_c (NTP4VC_RSE_Left c e2) +
             ntp4vc_rse_size_e e1) <
          (&2:int) *
            (ntp4vc_rse_size_c c +
             ntp4vc_rse_size_e (NTP4VC_RSE_Sub e1 e2))))`;;

let ntp4vc_rse_eval_premise =
  new_recursive_definition ntp4vc_rse_expr_RECURSION
   `(!n:int.
     !c:ntp4vc_rse_context.
     !result:int.
       ntp4vc_rse_eval_premise (NTP4VC_RSE_Cte n) c result <=>
       result =
         ntp4vc_rse_eval0
           (ntp4vc_rse_recompose c (NTP4VC_RSE_Cte n))) /\
    (!e1 e2:ntp4vc_rse_expr.
     !c:ntp4vc_rse_context.
     !result:int.
       ntp4vc_rse_eval_premise
         (NTP4VC_RSE_Sub e1 e2) c result <=>
       result =
         ntp4vc_rse_eval0
           (ntp4vc_rse_recompose (NTP4VC_RSE_Left c e2) e1))`;;

let statement =
  `!e:ntp4vc_rse_expr.
   !c:ntp4vc_rse_context.
     ntp4vc_rse_measure_condition e c /\
     (!result:int.
        ntp4vc_rse_eval_premise e c result
        ==>
        result = ntp4vc_rse_eval0 (ntp4vc_rse_recompose c e))`;;
