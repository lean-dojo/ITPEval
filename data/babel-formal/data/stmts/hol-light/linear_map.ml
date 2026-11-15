let is_linear_map = new_definition
  `is_linear_map (zeroV:'v) (addV:'v->'v->'v) (smul:'r->'v->'v)
                 (zeroW:'w) (addW:'w->'w->'w) (smulW:'r->'w->'w)
                 (toFun:'v->'w) <=>
     (!u v. addV u v = addV v u) /\
     (!u v w. addV (addV u v) w = addV u (addV v w)) /\
     (!u. addV u zeroV = u) /\
     (!a. smul a zeroV = zeroV) /\
     (!u v. addW u v = addW v u) /\
     (!u v w. addW (addW u v) w = addW u (addW v w)) /\
     (!u. addW u zeroW = u) /\
     (!a. smulW a zeroW = zeroW) /\
     (!u v. toFun (addV u v) = addW (toFun u) (toFun v)) /\
     (!a u. toFun (smul a u) = smulW a (toFun u))`;;

let ker = new_definition
  `ker (toFun:'v->'w) (zeroW:'w) x <=> toFun x = zeroW`;;

let im = new_definition
  `im (toFun:'v->'w) y <=> ?x. toFun x = y`;;

let ker_add =
  `!zeroV addV smul zeroW addW smulW (toFun:'v->'w) x y.
      is_linear_map zeroV addV smul zeroW addW smulW toFun ==>
      ker toFun zeroW x ==> ker toFun zeroW y ==> ker toFun zeroW (addV x y)`;;

let ker_smul =
  `!zeroV addV smul zeroW addW smulW (toFun:'v->'w) a x.
      is_linear_map zeroV addV smul zeroW addW smulW toFun ==>
      ker toFun zeroW x ==> ker toFun zeroW (smul a x)`;;

let im_add =
  `!zeroV addV smul zeroW addW smulW (toFun:'v->'w) y z.
      is_linear_map zeroV addV smul zeroW addW smulW toFun ==>
      im toFun y ==> im toFun z ==> im toFun (addW y z)`;;

let im_smul =
  `!zeroV addV smul zeroW addW smulW (toFun:'v->'w) a y.
      is_linear_map zeroV addV smul zeroW addW smulW toFun ==>
      im toFun y ==> im toFun (smulW a y)`;;

