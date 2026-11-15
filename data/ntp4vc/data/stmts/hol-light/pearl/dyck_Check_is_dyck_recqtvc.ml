(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/dyck_Check_is_dyck_recqtvc: a recursive verification condition for
  finding the unique maximal Dyck prefix of a parenthesis word. This file
  contains no proof.
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

let ntp4vc_dyck_unique = new_definition
  `ntp4vc_dyck_unique
     (x:ntp4vc_dyck_paren list)
     (p:ntp4vc_dyck_paren list)
     (s:ntp4vc_dyck_paren list) <=>
     !p2 s2:ntp4vc_dyck_paren list.
       x = APPEND p2 s2 /\ ntp4vc_dyck_fall p2 s2
       ==> p2 = p /\ s2 = s`;;

let ntp4vc_dyck_no_fall = new_definition
  `ntp4vc_dyck_no_fall (x:ntp4vc_dyck_paren list) <=>
     !p s:ntp4vc_dyck_paren list.
       x = APPEND p s ==> ~ntp4vc_dyck_fall p s`;;

let statement =
  `!w:ntp4vc_dyck_paren list.
     if ~(w = []) /\ HD w = NTP4VC_DYCK_L then
       ((&0:int) <= &(LENGTH w) /\ LENGTH (TL w) < LENGTH w) /\
       (!p0:ntp4vc_dyck_paren list.
          (!o1:ntp4vc_dyck_paren list.
             TL w = APPEND p0 o1 /\
             ntp4vc_dyck_fall p0 o1 /\
             ntp4vc_dyck_unique (TL w) p0 o1
             ==>
             (if o1 = [] then
                ntp4vc_dyck_no_fall w
              else
                ((&0:int) <= &(LENGTH w) /\
                 LENGTH (TL o1) < LENGTH w) /\
                (!p1:ntp4vc_dyck_paren list.
                   (!w2:ntp4vc_dyck_paren list.
                      TL o1 = APPEND p1 w2 /\
                      ntp4vc_dyck_fall p1 w2 /\
                      ntp4vc_dyck_unique (TL o1) p1 w2
                      ==>
                      w =
                        APPEND
                          (CONS NTP4VC_DYCK_L
                            (APPEND p0 (CONS NTP4VC_DYCK_R p1)))
                          w2 /\
                      ntp4vc_dyck_fall
                        (CONS NTP4VC_DYCK_L
                          (APPEND p0 (CONS NTP4VC_DYCK_R p1)))
                        w2 /\
                      ntp4vc_dyck_unique
                        w
                        (CONS NTP4VC_DYCK_L
                          (APPEND p0 (CONS NTP4VC_DYCK_R p1)))
                        w2) /\
                   (ntp4vc_dyck_no_fall (TL o1)
                    ==> ntp4vc_dyck_no_fall w)))) /\
          (ntp4vc_dyck_no_fall (TL w)
           ==> ntp4vc_dyck_no_fall w))
     else
       w = APPEND [] w /\
       ntp4vc_dyck_fall [] w /\
       ntp4vc_dyck_unique w [] w`;;
