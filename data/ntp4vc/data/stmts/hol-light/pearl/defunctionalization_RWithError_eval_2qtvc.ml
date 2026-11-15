(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/defunctionalization_RWithError_eval_2qtvc: an underflow-aware
  continuation-context verification condition for evaluating a nonnegative
  integer constant, asserting structural measure decrease and preservation of
  the error-aware semantics of the recomposed expression. This file contains
  no proof.
*)

let ntp4vc_rwe2_expr_INDUCT,ntp4vc_rwe2_expr_RECURSION = define_type
  "ntp4vc_rwe2_expr =
       NTP4VC_RWE2_Cte int
     | NTP4VC_RWE2_Sub ntp4vc_rwe2_expr ntp4vc_rwe2_expr";;

let ntp4vc_rwe2_value_INDUCT,ntp4vc_rwe2_value_RECURSION = define_type
  "ntp4vc_rwe2_value =
       NTP4VC_RWE2_Vnum int
     | NTP4VC_RWE2_Underflow";;

let ntp4vc_rwe2_context_INDUCT,ntp4vc_rwe2_context_RECURSION = define_type
  "ntp4vc_rwe2_context =
       NTP4VC_RWE2_Empty
     | NTP4VC_RWE2_Left ntp4vc_rwe2_context ntp4vc_rwe2_expr
     | NTP4VC_RWE2_Right int ntp4vc_rwe2_context";;

let ntp4vc_rwe2_size_e =
  new_recursive_definition ntp4vc_rwe2_expr_RECURSION
   `(!n:int.
       ntp4vc_rwe2_size_e (NTP4VC_RWE2_Cte n) = (&1:int)) /\
    (!e1 e2:ntp4vc_rwe2_expr.
       ntp4vc_rwe2_size_e (NTP4VC_RWE2_Sub e1 e2) =
       (&3:int) + ntp4vc_rwe2_size_e e1 + ntp4vc_rwe2_size_e e2)`;;

let ntp4vc_rwe2_sub_from =
  new_recursive_definition ntp4vc_rwe2_value_RECURSION
   `(!v1:int.
       ntp4vc_rwe2_sub_from NTP4VC_RWE2_Underflow v1 =
       NTP4VC_RWE2_Underflow) /\
    (!v2 v1:int.
       ntp4vc_rwe2_sub_from (NTP4VC_RWE2_Vnum v2) v1 =
       (if v2 <= v1
        then NTP4VC_RWE2_Vnum (v1 - v2)
        else NTP4VC_RWE2_Underflow))`;;

let ntp4vc_rwe2_sub_value =
  new_recursive_definition ntp4vc_rwe2_value_RECURSION
   `(!v2:ntp4vc_rwe2_value.
       ntp4vc_rwe2_sub_value NTP4VC_RWE2_Underflow v2 =
       NTP4VC_RWE2_Underflow) /\
    (!v1:int.
     !v2:ntp4vc_rwe2_value.
       ntp4vc_rwe2_sub_value (NTP4VC_RWE2_Vnum v1) v2 =
       ntp4vc_rwe2_sub_from v2 v1)`;;

let ntp4vc_rwe2_eval0 =
  new_recursive_definition ntp4vc_rwe2_expr_RECURSION
   `(!n:int.
       ntp4vc_rwe2_eval0 (NTP4VC_RWE2_Cte n) =
       (if (&0:int) <= n
        then NTP4VC_RWE2_Vnum n
        else NTP4VC_RWE2_Underflow)) /\
    (!e1 e2:ntp4vc_rwe2_expr.
       ntp4vc_rwe2_eval0 (NTP4VC_RWE2_Sub e1 e2) =
       ntp4vc_rwe2_sub_value
         (ntp4vc_rwe2_eval0 e1) (ntp4vc_rwe2_eval0 e2))`;;

let ntp4vc_rwe2_size_c =
  new_recursive_definition ntp4vc_rwe2_context_RECURSION
   `(ntp4vc_rwe2_size_c NTP4VC_RWE2_Empty = (&0:int)) /\
    (!c1:ntp4vc_rwe2_context.
     !e:ntp4vc_rwe2_expr.
       ntp4vc_rwe2_size_c (NTP4VC_RWE2_Left c1 e) =
       (&2:int) + ntp4vc_rwe2_size_c c1 + ntp4vc_rwe2_size_e e) /\
    (!n:int.
     !c1:ntp4vc_rwe2_context.
       ntp4vc_rwe2_size_c (NTP4VC_RWE2_Right n c1) =
       (&1:int) + ntp4vc_rwe2_size_c c1)`;;

let ntp4vc_rwe2_recompose =
  new_recursive_definition ntp4vc_rwe2_context_RECURSION
   `(!e:ntp4vc_rwe2_expr.
       ntp4vc_rwe2_recompose NTP4VC_RWE2_Empty e = e) /\
    (!c1:ntp4vc_rwe2_context.
     !e2 e:ntp4vc_rwe2_expr.
       ntp4vc_rwe2_recompose (NTP4VC_RWE2_Left c1 e2) e =
       ntp4vc_rwe2_recompose c1 (NTP4VC_RWE2_Sub e e2)) /\
    (!n1:int.
     !c1:ntp4vc_rwe2_context.
     !e:ntp4vc_rwe2_expr.
       ntp4vc_rwe2_recompose (NTP4VC_RWE2_Right n1 c1) e =
       ntp4vc_rwe2_recompose c1
         (NTP4VC_RWE2_Sub (NTP4VC_RWE2_Cte n1) e))`;;

let ntp4vc_rwe2_measure_case =
  new_recursive_definition ntp4vc_rwe2_context_RECURSION
   `(!n:int.
       ntp4vc_rwe2_measure_case NTP4VC_RWE2_Empty n = T) /\
    (!c1:ntp4vc_rwe2_context.
     !e:ntp4vc_rwe2_expr.
     !n:int.
       ntp4vc_rwe2_measure_case (NTP4VC_RWE2_Left c1 e) n =
       ((&0:int) <=
          (&1:int) +
          (&2:int) *
            ntp4vc_rwe2_size_c (NTP4VC_RWE2_Left c1 e) /\
        (&2:int) *
            (ntp4vc_rwe2_size_c (NTP4VC_RWE2_Right n c1) +
             ntp4vc_rwe2_size_e e) <
          (&1:int) +
          (&2:int) *
            ntp4vc_rwe2_size_c (NTP4VC_RWE2_Left c1 e))) /\
    (!n1:int.
     !c1:ntp4vc_rwe2_context.
     !n:int.
       ntp4vc_rwe2_measure_case (NTP4VC_RWE2_Right n1 c1) n =
       (n <= n1
        ==>
        ((&0:int) <=
           (&1:int) +
           (&2:int) *
             ntp4vc_rwe2_size_c (NTP4VC_RWE2_Right n1 c1) /\
         (&2:int) *
             (ntp4vc_rwe2_size_c c1 +
              ntp4vc_rwe2_size_e (NTP4VC_RWE2_Cte (n1 - n))) <
           (&1:int) +
           (&2:int) *
             ntp4vc_rwe2_size_c (NTP4VC_RWE2_Right n1 c1))))`;;

let ntp4vc_rwe2_result_case =
  new_recursive_definition ntp4vc_rwe2_context_RECURSION
   `(!n:int.
     !result:ntp4vc_rwe2_value.
       ntp4vc_rwe2_result_case NTP4VC_RWE2_Empty n result =
       result = NTP4VC_RWE2_Vnum n) /\
    (!c1:ntp4vc_rwe2_context.
     !e:ntp4vc_rwe2_expr.
     !n:int.
     !result:ntp4vc_rwe2_value.
       ntp4vc_rwe2_result_case (NTP4VC_RWE2_Left c1 e) n result =
       result =
         ntp4vc_rwe2_eval0
           (ntp4vc_rwe2_recompose (NTP4VC_RWE2_Right n c1) e)) /\
    (!n1:int.
     !c1:ntp4vc_rwe2_context.
     !n:int.
     !result:ntp4vc_rwe2_value.
       ntp4vc_rwe2_result_case
         (NTP4VC_RWE2_Right n1 c1) n result =
       (if n <= n1
        then result =
             ntp4vc_rwe2_eval0
               (ntp4vc_rwe2_recompose c1
                 (NTP4VC_RWE2_Cte (n1 - n)))
        else result = NTP4VC_RWE2_Underflow))`;;

let statement =
  `!n:int.
   !c:ntp4vc_rwe2_context.
     (&0:int) <= n
     ==>
     ntp4vc_rwe2_measure_case c n /\
     (!result:ntp4vc_rwe2_value.
        ntp4vc_rwe2_result_case c n result
        ==>
        result =
          ntp4vc_rwe2_eval0
            (ntp4vc_rwe2_recompose c (NTP4VC_RWE2_Cte n)))`;;
