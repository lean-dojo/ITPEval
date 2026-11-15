(*
  Statement-only formalization of VERINA corpus artifact verina_basic_54
  (verina__hol-light__verina_basic_54), catalog title "CanyonSearch": an
  executable two-pointer scan computes the minimum absolute difference between
  elements of two nonempty nondecreasing integer arrays, together with its
  exact minimum-and-attainment correctness contract. This file contains no
  proof.
*)

let canyonSearch_getDefault = new_definition
  `canyonSearch_getDefault (xs:int list) (i:num) =
     if i < LENGTH xs then EL i xs else (&0:int)`;;

let canyonSearch_natAbsDiff = new_definition
  `canyonSearch_natAbsDiff (x:int) (y:int) =
     num_of_int (abs (x - y))`;;

let CanyonSearch_precond = new_definition
  `CanyonSearch_precond (a:int list) (b:int list) <=>
     0 < LENGTH a /\
     0 < LENGTH b /\
     PAIRWISE (\x y:int. x <= y) a /\
     PAIRWISE (\x y:int. x <= y) b`;;

let canyonSearchAuxFuel =
  new_recursive_definition num_RECURSION
    `(!a:int list. !b:int list. !m:num. !n:num. !d:num.
        canyonSearchAuxFuel 0 a b m n d = d) /\
     (!fuel:num. !a:int list. !b:int list. !m:num. !n:num. !d:num.
        canyonSearchAuxFuel (SUC fuel) a b m n d =
        if m < LENGTH a /\ n < LENGTH b then
          let diff =
            canyonSearch_natAbsDiff
              (canyonSearch_getDefault a m)
              (canyonSearch_getDefault b n) in
          let new_d = if diff < d then diff else d in
          if canyonSearch_getDefault a m <=
             canyonSearch_getDefault b n
          then
            canyonSearchAuxFuel fuel a b (m + 1) n new_d
          else
            canyonSearchAuxFuel fuel a b m (n + 1) new_d
        else
          d)`;;

let canyonSearchAux = new_definition
  `canyonSearchAux
      (a:int list) (b:int list) (m:num) (n:num) (d:num) =
     canyonSearchAuxFuel
       (LENGTH a + LENGTH b - m - n) a b m n d`;;

let CanyonSearch = new_definition
  `CanyonSearch (a:int list) (b:int list) =
     let a0 = canyonSearch_getDefault a 0 in
     let b0 = canyonSearch_getDefault b 0 in
     let init =
       if a0 < b0 then canyonSearch_natAbsDiff b0 a0
       else canyonSearch_natAbsDiff a0 b0 in
     canyonSearchAux a b 0 0 init`;;

let CanyonSearch_postcond = new_definition
  `CanyonSearch_postcond
      (a:int list) (b:int list) (result:num) <=>
     (?ai:int. ?bi:int.
        MEM ai a /\
        MEM bi b /\
        result = canyonSearch_natAbsDiff ai bi) /\
     (!ai:int. !bi:int.
        MEM ai a /\ MEM bi b
        ==> result <= canyonSearch_natAbsDiff ai bi)`;;

let CanyonSearch_spec_satisfied =
  `!a:int list. !b:int list.
     CanyonSearch_precond a b
     ==> CanyonSearch_postcond a b (CanyonSearch a b)`;;
