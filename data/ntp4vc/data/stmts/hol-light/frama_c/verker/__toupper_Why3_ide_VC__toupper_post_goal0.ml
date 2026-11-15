(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/__toupper_Why3_ide_VC__toupper_post_goal0:
  a C toupper postcondition verification condition relating an unsigned byte,
  its signed-byte lowercase test, and the unchanged or case-shifted output
  selected by a Boolean integer. This file contains no proof.
*)

let statement =
  `!to_sint8 to_uint8 l_tolower l_toupper:int->int.
   !i_1 i i_2:int.
     let is_uint8 =
       \z:int.
         (&0:int) <= z /\ z < (&256:int) in
     let is_sint8 =
       \z:int.
         --(&128:int) <= z /\ z < (&128:int) in
     let p_islower =
       \c:int.
         (&97:int) <= c /\ c <= (&122:int) in
     (!z:int. is_sint8 (to_sint8 z))
     ==> (!z:int. is_sint8 z ==> to_sint8 z = z)
     ==> (!z:int. is_uint8 (to_uint8 z))
     ==> (!z:int. is_uint8 z ==> to_uint8 z = z)
     ==> (!z:int. to_sint8 (to_sint8 z) = to_sint8 z)
     ==> (!z:int. to_uint8 (to_uint8 z) = to_uint8 z)
     ==> (!z:int. to_sint8 (to_uint8 z) = to_sint8 z)
     ==> l_tolower (&65:int) = (&97:int)
     ==> l_tolower (&66:int) = (&98:int)
     ==> l_tolower (&67:int) = (&99:int)
     ==> l_tolower (&68:int) = (&100:int)
     ==> l_tolower (&69:int) = (&101:int)
     ==> l_tolower (&70:int) = (&102:int)
     ==> l_tolower (&71:int) = (&103:int)
     ==> l_tolower (&72:int) = (&104:int)
     ==> l_tolower (&73:int) = (&105:int)
     ==> l_tolower (&74:int) = (&106:int)
     ==> l_tolower (&75:int) = (&107:int)
     ==> l_tolower (&76:int) = (&108:int)
     ==> l_tolower (&77:int) = (&109:int)
     ==> l_tolower (&78:int) = (&110:int)
     ==> l_tolower (&79:int) = (&111:int)
     ==> l_tolower (&80:int) = (&112:int)
     ==> l_tolower (&81:int) = (&113:int)
     ==> l_tolower (&82:int) = (&114:int)
     ==> l_tolower (&83:int) = (&115:int)
     ==> l_tolower (&84:int) = (&116:int)
     ==> l_tolower (&85:int) = (&117:int)
     ==> l_tolower (&86:int) = (&118:int)
     ==> l_tolower (&87:int) = (&119:int)
     ==> l_tolower (&88:int) = (&120:int)
     ==> l_tolower (&89:int) = (&121:int)
     ==> l_tolower (&90:int) = (&122:int)
     ==> (!c:int. ~p_islower c ==> l_toupper c = c)
     ==> (!c:int.
            ~p_islower c
            ==> l_toupper (l_tolower c) = c)
     ==> (p_islower (to_sint8 i_1) <=> ~(i = (&0:int)))
     ==> is_uint8 i
     ==> is_uint8 i_1
     ==> is_uint8 i_2
     ==> (if i = (&0:int)
          then i_2 = i_1
          else to_uint8 (i_1 - (&32:int)) = i_2)
     ==> l_toupper i_1 = i_2`;;
