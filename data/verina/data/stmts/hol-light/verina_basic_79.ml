(*
  Statement-only formalization of VERINA corpus artifact verina_basic_79
  (verina__hol-light__verina_basic_79), catalog title "onlineMax": an
  executable scan computes the maximum of an initial nonempty segment of an
  integer array and then finds the first later element exceeding it, or the
  array's last index if none does, together with its correctness contract.
  This file contains no proof.
*)

let onlineMax_getDefault = new_definition
  `onlineMax_getDefault (a:int list) (i:num) =
     if i < LENGTH a then EL i a else (&0:int)`;;

let onlineMax_precond = new_definition
  `onlineMax_precond (a:int list) (x:num) <=>
     0 < LENGTH a /\
     0 < x /\
     x < LENGTH a`;;

let findBestFuel =
  new_recursive_definition num_RECURSION
    `(!a:int list. !x:num. !i:num. !best:int.
        findBestFuel 0 a x i best = best) /\
     (!fuel:num. !a:int list. !x:num. !i:num. !best:int.
        findBestFuel (SUC fuel) a x i best =
        if i < x then
          let newBest =
            if onlineMax_getDefault a i > best then
              onlineMax_getDefault a i
            else
              best in
          findBestFuel fuel a x (i + 1) newBest
        else
          best)`;;

let findBest = new_definition
  `findBest
      (a:int list) (x:num) (i:num) (best:int) =
     findBestFuel (x - i) a x i best`;;

let findPFuel =
  new_recursive_definition num_RECURSION
    `(!a:int list. !x:num. !m:int. !i:num.
        findPFuel 0 a x m i = LENGTH a - 1) /\
     (!fuel:num. !a:int list. !x:num. !m:int. !i:num.
        findPFuel (SUC fuel) a x m i =
        if i < LENGTH a then
          if onlineMax_getDefault a i > m then
            i
          else
            findPFuel fuel a x m (i + 1)
        else
          LENGTH a - 1)`;;

let findP = new_definition
  `findP
      (a:int list) (x:num) (m:int) (i:num) =
     findPFuel (LENGTH a - i) a x m i`;;

let onlineMax = new_definition
  `onlineMax (a:int list) (x:num) =
     let best = onlineMax_getDefault a 0 in
     let m = findBest a x 1 best in
     let p = findP a x m x in
     (m,p)`;;

let onlineMax_postcond = new_definition
  `onlineMax_postcond
      (a:int list) (x:num) (result:int#num) <=>
     let m = FST result in
     let p = SND result in
     (x <= p /\ p < LENGTH a) /\
     (!i:num.
        i < x
        ==> onlineMax_getDefault a i <= m) /\
     (?i:num.
        i < x /\
        onlineMax_getDefault a i = m) /\
     (!i:num.
        x <= i
        ==> i < p
        ==> onlineMax_getDefault a i <= m) /\
     (onlineMax_getDefault a p > m \/
      (p = LENGTH a - 1 /\
       (!i:num.
          x <= i
          ==> i < LENGTH a
          ==> onlineMax_getDefault a i <= m)))`;;

let onlineMax_spec_satisfied =
  `!a:int list. !x:num.
     onlineMax_precond a x
     ==> onlineMax_postcond a x (onlineMax a x)`;;
