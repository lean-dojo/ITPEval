(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/dyck_Check_is_dyckqtvc: a verification condition characterizing a
  Dyck word using its unique maximal Dyck prefix, or the absence of such a
  prefix. This file contains no proof.
*)

let ntp4vc_dyck_paren_INDUCT,ntp4vc_dyck_paren_RECURSION = define_type
  "ntp4vc_dyck_paren =
       NTP4VC_DYCK_L
     | NTP4VC_DYCK_R";;

let ntp4vc_dyck_RULES,ntp4vc_dyck_INDUCT,ntp4vc_dyck_CASES =
  new_inductive_definition
   `(ntp4vc_dyck ([]:ntp4vc_dyck_paren list)) /\
    (!w1 w2:ntp4vc_dyck_paren list.
       ntp4vc_dyck w1 /\ ntp4vc_dyck w2
       ==>
       ntp4vc_dyck
         (CONS NTP4VC_DYCK_L
           (APPEND w1 (CONS NTP4VC_DYCK_R w2))))`;;

let ntp4vc_dyck_fall = new_definition
  `ntp4vc_dyck_fall
     (p:ntp4vc_dyck_paren list) (s:ntp4vc_dyck_paren list) <=>
     ntp4vc_dyck p /\
     (if s = [] then T else ~(HD s = NTP4VC_DYCK_L))`;;

let statement =
  `!w o2:ntp4vc_dyck_paren list.
     ((!o1:ntp4vc_dyck_paren list.
         w = APPEND o2 o1 /\
         ntp4vc_dyck_fall o2 o1 /\
         (!p2 s:ntp4vc_dyck_paren list.
            w = APPEND p2 s /\ ntp4vc_dyck_fall p2 s
            ==> p2 = o2 /\ s = o1)
         ==>
         !result:bool.
           (if o1 = [] then result = T else result = F)
           ==> (result = T <=> ntp4vc_dyck w)) /\
      ((!p s:ntp4vc_dyck_paren list.
          w = APPEND p s ==> ~ntp4vc_dyck_fall p s)
       ==> ~ntp4vc_dyck w))`;;
