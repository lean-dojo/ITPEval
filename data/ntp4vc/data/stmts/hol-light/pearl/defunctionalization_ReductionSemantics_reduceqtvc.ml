(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/defunctionalization_ReductionSemantics_reduceqtvc: a
  reduction-semantics verification condition stating that replacing a
  subtraction redex by an expression with the same direct integer evaluation
  preserves evaluation after recomposition in an arbitrary context. This file
  contains no proof.
*)

let ntp4vc_reduce_expr_INDUCT,ntp4vc_reduce_expr_RECURSION = define_type
  "ntp4vc_reduce_expr =
       NTP4VC_Reduce_Cte int
     | NTP4VC_Reduce_Sub ntp4vc_reduce_expr ntp4vc_reduce_expr";;

let ntp4vc_reduce_context_INDUCT,ntp4vc_reduce_context_RECURSION = define_type
  "ntp4vc_reduce_context =
       NTP4VC_Reduce_Empty
     | NTP4VC_Reduce_Left ntp4vc_reduce_context ntp4vc_reduce_expr
     | NTP4VC_Reduce_Right int ntp4vc_reduce_context";;

let ntp4vc_reduce_eval0 =
  new_recursive_definition ntp4vc_reduce_expr_RECURSION
   `(!n:int.
       ntp4vc_reduce_eval0 (NTP4VC_Reduce_Cte n) = n) /\
    (!e1 e2:ntp4vc_reduce_expr.
       ntp4vc_reduce_eval0 (NTP4VC_Reduce_Sub e1 e2) =
       ntp4vc_reduce_eval0 e1 - ntp4vc_reduce_eval0 e2)`;;

let ntp4vc_reduce_is_redex =
  new_recursive_definition ntp4vc_reduce_expr_RECURSION
   `(!n:int.
       ntp4vc_reduce_is_redex (NTP4VC_Reduce_Cte n) = F) /\
    (!e1 e2:ntp4vc_reduce_expr.
       ntp4vc_reduce_is_redex (NTP4VC_Reduce_Sub e1 e2) =
       ((?n1:int. e1 = NTP4VC_Reduce_Cte n1) /\
        (?n2:int. e2 = NTP4VC_Reduce_Cte n2)))`;;

let ntp4vc_reduce_recompose =
  new_recursive_definition ntp4vc_reduce_context_RECURSION
   `(!e:ntp4vc_reduce_expr.
       ntp4vc_reduce_recompose NTP4VC_Reduce_Empty e = e) /\
    (!c1:ntp4vc_reduce_context.
     !e2 e:ntp4vc_reduce_expr.
       ntp4vc_reduce_recompose (NTP4VC_Reduce_Left c1 e2) e =
       ntp4vc_reduce_recompose c1 (NTP4VC_Reduce_Sub e e2)) /\
    (!n1:int.
     !c1:ntp4vc_reduce_context.
     !e:ntp4vc_reduce_expr.
       ntp4vc_reduce_recompose (NTP4VC_Reduce_Right n1 c1) e =
       ntp4vc_reduce_recompose c1
         (NTP4VC_Reduce_Sub (NTP4VC_Reduce_Cte n1) e))`;;

let statement =
  `!c:ntp4vc_reduce_context.
   !r e:ntp4vc_reduce_expr.
     ntp4vc_reduce_recompose c r = e
     ==>
     ntp4vc_reduce_is_redex r
     ==>
     ntp4vc_reduce_is_redex r /\
     (!result:ntp4vc_reduce_expr.
        (?o1:ntp4vc_reduce_expr.
           ntp4vc_reduce_eval0 o1 = ntp4vc_reduce_eval0 r /\
           result = ntp4vc_reduce_recompose c o1)
        ==>
        ntp4vc_reduce_eval0 result = ntp4vc_reduce_eval0 e)`;;
