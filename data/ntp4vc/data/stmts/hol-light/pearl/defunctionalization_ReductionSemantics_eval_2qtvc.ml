(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/defunctionalization_ReductionSemantics_eval_2qtvc: a
  reduction-semantics verification condition for evaluating an integer value
  within an arithmetic-expression context, asserting structural measure
  decrease and preservation of direct integer evaluation. This file contains
  no proof.
*)

let ntp4vc_rse2_expr_INDUCT,ntp4vc_rse2_expr_RECURSION = define_type
  "ntp4vc_rse2_expr =
       NTP4VC_RSE2_Cte int
     | NTP4VC_RSE2_Sub ntp4vc_rse2_expr ntp4vc_rse2_expr";;

let ntp4vc_rse2_context_INDUCT,ntp4vc_rse2_context_RECURSION = define_type
  "ntp4vc_rse2_context =
       NTP4VC_RSE2_Empty
     | NTP4VC_RSE2_Left ntp4vc_rse2_context ntp4vc_rse2_expr
     | NTP4VC_RSE2_Right int ntp4vc_rse2_context";;

let ntp4vc_rse2_eval0 =
  new_recursive_definition ntp4vc_rse2_expr_RECURSION
   `(!n:int.
       ntp4vc_rse2_eval0 (NTP4VC_RSE2_Cte n) = n) /\
    (!e1 e2:ntp4vc_rse2_expr.
       ntp4vc_rse2_eval0 (NTP4VC_RSE2_Sub e1 e2) =
       ntp4vc_rse2_eval0 e1 - ntp4vc_rse2_eval0 e2)`;;

let ntp4vc_rse2_size_e =
  new_recursive_definition ntp4vc_rse2_expr_RECURSION
   `(!n:int.
       ntp4vc_rse2_size_e (NTP4VC_RSE2_Cte n) = (&1:int)) /\
    (!e1 e2:ntp4vc_rse2_expr.
       ntp4vc_rse2_size_e (NTP4VC_RSE2_Sub e1 e2) =
       (&3:int) + ntp4vc_rse2_size_e e1 + ntp4vc_rse2_size_e e2)`;;

let ntp4vc_rse2_size_c =
  new_recursive_definition ntp4vc_rse2_context_RECURSION
   `(ntp4vc_rse2_size_c NTP4VC_RSE2_Empty = (&0:int)) /\
    (!c1:ntp4vc_rse2_context.
     !e:ntp4vc_rse2_expr.
       ntp4vc_rse2_size_c (NTP4VC_RSE2_Left c1 e) =
       (&2:int) + ntp4vc_rse2_size_c c1 + ntp4vc_rse2_size_e e) /\
    (!n:int.
     !c1:ntp4vc_rse2_context.
       ntp4vc_rse2_size_c (NTP4VC_RSE2_Right n c1) =
       (&1:int) + ntp4vc_rse2_size_c c1)`;;

let ntp4vc_rse2_recompose =
  new_recursive_definition ntp4vc_rse2_context_RECURSION
   `(!e:ntp4vc_rse2_expr.
       ntp4vc_rse2_recompose NTP4VC_RSE2_Empty e = e) /\
    (!c1:ntp4vc_rse2_context.
     !e2 e:ntp4vc_rse2_expr.
       ntp4vc_rse2_recompose (NTP4VC_RSE2_Left c1 e2) e =
       ntp4vc_rse2_recompose c1 (NTP4VC_RSE2_Sub e e2)) /\
    (!n1:int.
     !c1:ntp4vc_rse2_context.
     !e:ntp4vc_rse2_expr.
       ntp4vc_rse2_recompose (NTP4VC_RSE2_Right n1 c1) e =
       ntp4vc_rse2_recompose c1
         (NTP4VC_RSE2_Sub (NTP4VC_RSE2_Cte n1) e))`;;

let ntp4vc_rse2_measure_case =
  new_recursive_definition ntp4vc_rse2_context_RECURSION
   `(!n:int.
       ntp4vc_rse2_measure_case NTP4VC_RSE2_Empty n = T) /\
    (!c1:ntp4vc_rse2_context.
     !e:ntp4vc_rse2_expr.
     !n:int.
       ntp4vc_rse2_measure_case (NTP4VC_RSE2_Left c1 e) n =
       ((&0:int) <=
          (&1:int) +
          (&2:int) *
            ntp4vc_rse2_size_c (NTP4VC_RSE2_Left c1 e) /\
        (&2:int) *
            (ntp4vc_rse2_size_c (NTP4VC_RSE2_Right n c1) +
             ntp4vc_rse2_size_e e) <
          (&1:int) +
          (&2:int) *
            ntp4vc_rse2_size_c (NTP4VC_RSE2_Left c1 e))) /\
    (!n1:int.
     !c1:ntp4vc_rse2_context.
     !n:int.
       ntp4vc_rse2_measure_case (NTP4VC_RSE2_Right n1 c1) n =
       ((&0:int) <=
          (&1:int) +
          (&2:int) *
            ntp4vc_rse2_size_c (NTP4VC_RSE2_Right n1 c1) /\
        (&2:int) *
            (ntp4vc_rse2_size_c c1 +
             ntp4vc_rse2_size_e (NTP4VC_RSE2_Cte (n1 - n))) <
          (&1:int) +
          (&2:int) *
            ntp4vc_rse2_size_c (NTP4VC_RSE2_Right n1 c1)))`;;

let ntp4vc_rse2_result_case =
  new_recursive_definition ntp4vc_rse2_context_RECURSION
   `(!n result:int.
       ntp4vc_rse2_result_case NTP4VC_RSE2_Empty n result =
       (result = n)) /\
    (!c1:ntp4vc_rse2_context.
     !e:ntp4vc_rse2_expr.
     !n result:int.
       ntp4vc_rse2_result_case (NTP4VC_RSE2_Left c1 e) n result =
       (result =
        ntp4vc_rse2_eval0
          (ntp4vc_rse2_recompose (NTP4VC_RSE2_Right n c1) e))) /\
    (!n1:int.
     !c1:ntp4vc_rse2_context.
     !n result:int.
       ntp4vc_rse2_result_case
         (NTP4VC_RSE2_Right n1 c1) n result =
       (result =
        ntp4vc_rse2_eval0
          (ntp4vc_rse2_recompose c1
            (NTP4VC_RSE2_Cte (n1 - n)))))`;;

let statement =
  `!c:ntp4vc_rse2_context.
   !n:int.
     ntp4vc_rse2_measure_case c n /\
     (!result:int.
        ntp4vc_rse2_result_case c n result
        ==>
        result =
          ntp4vc_rse2_eval0
            (ntp4vc_rse2_recompose c (NTP4VC_RSE2_Cte n)))`;;
