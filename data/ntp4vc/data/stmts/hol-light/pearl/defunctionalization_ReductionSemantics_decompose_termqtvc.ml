(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/defunctionalization_ReductionSemantics_decompose_termqtvc: a
  reduction-semantics verification condition for decomposing an arithmetic
  expression term, preserving redex recomposition while decreasing a
  structural measure. This file contains no proof.
*)

let ntp4vc_rst_expr_INDUCT,ntp4vc_rst_expr_RECURSION = define_type
  "ntp4vc_rst_expr =
       NTP4VC_RST_Cte int
     | NTP4VC_RST_Sub ntp4vc_rst_expr ntp4vc_rst_expr";;

let ntp4vc_rst_context_INDUCT,ntp4vc_rst_context_RECURSION = define_type
  "ntp4vc_rst_context =
       NTP4VC_RST_Empty
     | NTP4VC_RST_Left ntp4vc_rst_context ntp4vc_rst_expr
     | NTP4VC_RST_Right int ntp4vc_rst_context";;

let ntp4vc_rst_is_value =
  new_recursive_definition ntp4vc_rst_expr_RECURSION
   `(!n:int.
       ntp4vc_rst_is_value (NTP4VC_RST_Cte n) = T) /\
    (!e1 e2:ntp4vc_rst_expr.
       ntp4vc_rst_is_value (NTP4VC_RST_Sub e1 e2) = F)`;;

let ntp4vc_rst_is_redex =
  new_recursive_definition ntp4vc_rst_expr_RECURSION
   `(!n:int.
       ntp4vc_rst_is_redex (NTP4VC_RST_Cte n) = F) /\
    (!e1 e2:ntp4vc_rst_expr.
       ntp4vc_rst_is_redex (NTP4VC_RST_Sub e1 e2) =
       (ntp4vc_rst_is_value e1 /\ ntp4vc_rst_is_value e2))`;;

let ntp4vc_rst_is_empty_context =
  new_recursive_definition ntp4vc_rst_context_RECURSION
   `(ntp4vc_rst_is_empty_context NTP4VC_RST_Empty = T) /\
    (!c1:ntp4vc_rst_context.
     !e:ntp4vc_rst_expr.
       ntp4vc_rst_is_empty_context (NTP4VC_RST_Left c1 e) = F) /\
    (!n:int.
     !c1:ntp4vc_rst_context.
       ntp4vc_rst_is_empty_context (NTP4VC_RST_Right n c1) = F)`;;

let ntp4vc_rst_size_e =
  new_recursive_definition ntp4vc_rst_expr_RECURSION
   `(!n:int.
       ntp4vc_rst_size_e (NTP4VC_RST_Cte n) = (&1:int)) /\
    (!e1 e2:ntp4vc_rst_expr.
       ntp4vc_rst_size_e (NTP4VC_RST_Sub e1 e2) =
       (&3:int) + ntp4vc_rst_size_e e1 + ntp4vc_rst_size_e e2)`;;

let ntp4vc_rst_size_c =
  new_recursive_definition ntp4vc_rst_context_RECURSION
   `(ntp4vc_rst_size_c NTP4VC_RST_Empty = (&0:int)) /\
    (!c1:ntp4vc_rst_context.
     !e:ntp4vc_rst_expr.
       ntp4vc_rst_size_c (NTP4VC_RST_Left c1 e) =
       (&2:int) + ntp4vc_rst_size_c c1 + ntp4vc_rst_size_e e) /\
    (!n:int.
     !c1:ntp4vc_rst_context.
       ntp4vc_rst_size_c (NTP4VC_RST_Right n c1) =
       (&1:int) + ntp4vc_rst_size_c c1)`;;

let ntp4vc_rst_recompose =
  new_recursive_definition ntp4vc_rst_context_RECURSION
   `(!e:ntp4vc_rst_expr.
       ntp4vc_rst_recompose NTP4VC_RST_Empty e = e) /\
    (!c1:ntp4vc_rst_context.
     !e2 e:ntp4vc_rst_expr.
       ntp4vc_rst_recompose (NTP4VC_RST_Left c1 e2) e =
       ntp4vc_rst_recompose c1 (NTP4VC_RST_Sub e e2)) /\
    (!n1:int.
     !c1:ntp4vc_rst_context.
     !e:ntp4vc_rst_expr.
       ntp4vc_rst_recompose (NTP4VC_RST_Right n1 c1) e =
       ntp4vc_rst_recompose c1
         (NTP4VC_RST_Sub (NTP4VC_RST_Cte n1) e))`;;

let ntp4vc_rst_decompose_term_case =
  new_recursive_definition ntp4vc_rst_expr_RECURSION
   `(!n:int.
     !c:ntp4vc_rst_context.
       ntp4vc_rst_decompose_term_case (NTP4VC_RST_Cte n) c =
       (((&0:int) <=
           ntp4vc_rst_size_e (NTP4VC_RST_Cte n) +
           ntp4vc_rst_size_c c /\
         ntp4vc_rst_size_c c <
           ntp4vc_rst_size_e (NTP4VC_RST_Cte n) +
           ntp4vc_rst_size_c c) /\
        (!c1:ntp4vc_rst_context.
         !e1:ntp4vc_rst_expr.
           ntp4vc_rst_recompose c1 e1 =
             ntp4vc_rst_recompose c (NTP4VC_RST_Cte n) /\
           ntp4vc_rst_is_redex e1
           ==>
           ntp4vc_rst_recompose c1 e1 =
             ntp4vc_rst_recompose c (NTP4VC_RST_Cte n) /\
           ntp4vc_rst_is_redex e1) /\
        (ntp4vc_rst_is_empty_context c
         ==>
         ntp4vc_rst_is_empty_context c /\
         ntp4vc_rst_is_value (NTP4VC_RST_Cte n)))) /\
    (!e1 e2:ntp4vc_rst_expr.
     !c:ntp4vc_rst_context.
       ntp4vc_rst_decompose_term_case (NTP4VC_RST_Sub e1 e2) c =
       (((&0:int) <=
           ntp4vc_rst_size_e (NTP4VC_RST_Sub e1 e2) +
           ntp4vc_rst_size_c c /\
         ntp4vc_rst_size_e e1 +
           ntp4vc_rst_size_c (NTP4VC_RST_Left c e2) <
           ntp4vc_rst_size_e (NTP4VC_RST_Sub e1 e2) +
           ntp4vc_rst_size_c c) /\
        (!c1:ntp4vc_rst_context.
         !e11:ntp4vc_rst_expr.
           ntp4vc_rst_recompose c1 e11 =
             ntp4vc_rst_recompose (NTP4VC_RST_Left c e2) e1 /\
           ntp4vc_rst_is_redex e11
           ==>
           ntp4vc_rst_recompose c1 e11 =
             ntp4vc_rst_recompose c (NTP4VC_RST_Sub e1 e2) /\
           ntp4vc_rst_is_redex e11) /\
        (ntp4vc_rst_is_empty_context (NTP4VC_RST_Left c e2) /\
         ntp4vc_rst_is_value e1
         ==>
         ntp4vc_rst_is_empty_context c /\
         ntp4vc_rst_is_value (NTP4VC_RST_Sub e1 e2))))`;;

let statement =
  `!e:ntp4vc_rst_expr.
   !c:ntp4vc_rst_context.
     ntp4vc_rst_decompose_term_case e c`;;
