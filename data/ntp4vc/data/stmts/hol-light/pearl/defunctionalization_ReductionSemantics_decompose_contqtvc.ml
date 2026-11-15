(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/defunctionalization_ReductionSemantics_decompose_contqtvc: a
  reduction-semantics verification condition for decomposing an arithmetic
  expression continuation, preserving recomposition while decreasing its
  structural measure. This file contains no proof.
*)

let ntp4vc_rs_expr_INDUCT,ntp4vc_rs_expr_RECURSION = define_type
  "ntp4vc_rs_expr =
       NTP4VC_RS_Cte int
     | NTP4VC_RS_Sub ntp4vc_rs_expr ntp4vc_rs_expr";;

let ntp4vc_rs_context_INDUCT,ntp4vc_rs_context_RECURSION = define_type
  "ntp4vc_rs_context =
       NTP4VC_RS_Empty
     | NTP4VC_RS_Left ntp4vc_rs_context ntp4vc_rs_expr
     | NTP4VC_RS_Right int ntp4vc_rs_context";;

let ntp4vc_rs_is_value =
  new_recursive_definition ntp4vc_rs_expr_RECURSION
   `(!n:int.
       ntp4vc_rs_is_value (NTP4VC_RS_Cte n) = T) /\
    (!e1 e2:ntp4vc_rs_expr.
       ntp4vc_rs_is_value (NTP4VC_RS_Sub e1 e2) = F)`;;

let ntp4vc_rs_is_redex =
  new_recursive_definition ntp4vc_rs_expr_RECURSION
   `(!n:int.
       ntp4vc_rs_is_redex (NTP4VC_RS_Cte n) = F) /\
    (!e1 e2:ntp4vc_rs_expr.
       ntp4vc_rs_is_redex (NTP4VC_RS_Sub e1 e2) =
       (ntp4vc_rs_is_value e1 /\ ntp4vc_rs_is_value e2))`;;

let ntp4vc_rs_is_empty_context =
  new_recursive_definition ntp4vc_rs_context_RECURSION
   `(ntp4vc_rs_is_empty_context NTP4VC_RS_Empty = T) /\
    (!c1:ntp4vc_rs_context.
     !e:ntp4vc_rs_expr.
       ntp4vc_rs_is_empty_context (NTP4VC_RS_Left c1 e) = F) /\
    (!n:int.
     !c1:ntp4vc_rs_context.
       ntp4vc_rs_is_empty_context (NTP4VC_RS_Right n c1) = F)`;;

let ntp4vc_rs_size_e =
  new_recursive_definition ntp4vc_rs_expr_RECURSION
   `(!n:int.
       ntp4vc_rs_size_e (NTP4VC_RS_Cte n) = (&1:int)) /\
    (!e1 e2:ntp4vc_rs_expr.
       ntp4vc_rs_size_e (NTP4VC_RS_Sub e1 e2) =
       (&3:int) + ntp4vc_rs_size_e e1 + ntp4vc_rs_size_e e2)`;;

let ntp4vc_rs_size_c =
  new_recursive_definition ntp4vc_rs_context_RECURSION
   `(ntp4vc_rs_size_c NTP4VC_RS_Empty = (&0:int)) /\
    (!c1:ntp4vc_rs_context.
     !e:ntp4vc_rs_expr.
       ntp4vc_rs_size_c (NTP4VC_RS_Left c1 e) =
       (&2:int) + ntp4vc_rs_size_c c1 + ntp4vc_rs_size_e e) /\
    (!n:int.
     !c1:ntp4vc_rs_context.
       ntp4vc_rs_size_c (NTP4VC_RS_Right n c1) =
       (&1:int) + ntp4vc_rs_size_c c1)`;;

let ntp4vc_rs_recompose =
  new_recursive_definition ntp4vc_rs_context_RECURSION
   `(!e:ntp4vc_rs_expr.
       ntp4vc_rs_recompose NTP4VC_RS_Empty e = e) /\
    (!c1:ntp4vc_rs_context.
     !e2 e:ntp4vc_rs_expr.
       ntp4vc_rs_recompose (NTP4VC_RS_Left c1 e2) e =
       ntp4vc_rs_recompose c1 (NTP4VC_RS_Sub e e2)) /\
    (!n1:int.
     !c1:ntp4vc_rs_context.
     !e:ntp4vc_rs_expr.
       ntp4vc_rs_recompose (NTP4VC_RS_Right n1 c1) e =
       ntp4vc_rs_recompose c1 (NTP4VC_RS_Sub (NTP4VC_RS_Cte n1) e))`;;

let ntp4vc_rs_decompose_cont_case =
  new_recursive_definition ntp4vc_rs_context_RECURSION
   `(!n:int.
       ntp4vc_rs_decompose_cont_case NTP4VC_RS_Empty n =
       ntp4vc_rs_is_empty_context NTP4VC_RS_Empty) /\
    (!c1:ntp4vc_rs_context.
     !e:ntp4vc_rs_expr.
     !n:int.
       ntp4vc_rs_decompose_cont_case (NTP4VC_RS_Left c1 e) n =
       (((&0:int) <= ntp4vc_rs_size_c (NTP4VC_RS_Left c1 e) /\
         ntp4vc_rs_size_e e +
           ntp4vc_rs_size_c (NTP4VC_RS_Right n c1) <
         ntp4vc_rs_size_c (NTP4VC_RS_Left c1 e)) /\
        (!c11:ntp4vc_rs_context.
         !e1:ntp4vc_rs_expr.
           ntp4vc_rs_recompose c11 e1 =
             ntp4vc_rs_recompose (NTP4VC_RS_Right n c1) e /\
           ntp4vc_rs_is_redex e1
           ==>
           ntp4vc_rs_recompose c11 e1 =
             ntp4vc_rs_recompose (NTP4VC_RS_Left c1 e)
               (NTP4VC_RS_Cte n) /\
           ntp4vc_rs_is_redex e1) /\
        (ntp4vc_rs_is_empty_context (NTP4VC_RS_Right n c1) /\
         ntp4vc_rs_is_value e
         ==>
         ntp4vc_rs_is_empty_context (NTP4VC_RS_Left c1 e)))) /\
    (!n1:int.
     !c1:ntp4vc_rs_context.
     !n:int.
       ntp4vc_rs_decompose_cont_case (NTP4VC_RS_Right n1 c1) n =
       (ntp4vc_rs_recompose c1
          (NTP4VC_RS_Sub (NTP4VC_RS_Cte n1) (NTP4VC_RS_Cte n)) =
        ntp4vc_rs_recompose (NTP4VC_RS_Right n1 c1)
          (NTP4VC_RS_Cte n) /\
        ntp4vc_rs_is_redex
          (NTP4VC_RS_Sub (NTP4VC_RS_Cte n1) (NTP4VC_RS_Cte n))))`;;

let statement =
  `!c:ntp4vc_rs_context.
   !n:int.
     ntp4vc_rs_decompose_cont_case c n`;;
