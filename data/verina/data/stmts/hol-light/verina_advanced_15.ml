(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_15,
  catalog title "increasingTriplet": an executable two-threshold list scan
  detects three increasing integers at increasing indices, together with its
  total precondition and indexed postcondition. This file contains no proof.
*)

let increasingTriplet_precond = new_definition
  `increasingTriplet_precond (nums:int list) <=> T`;;

let increasingTriplet_optionValue = new_definition
  `increasingTriplet_optionValue (value:int option) =
     @x:int. value = SOME x`;;

let increasingTriplet_loop =
  new_recursive_definition list_RECURSION
    `(increasingTriplet_loop
        ([]:int list) (first:int option) (second:int option) = F) /\
     (!x:int. !rest:int list.
      !first:int option. !second:int option.
        increasingTriplet_loop (CONS x rest) first second =
        if first = NONE then
          increasingTriplet_loop rest (SOME x) NONE
        else
          let f = increasingTriplet_optionValue first in
          if x <= f then
            increasingTriplet_loop rest (SOME x) second
          else if second = NONE then
            increasingTriplet_loop rest first (SOME x)
          else
            let s = increasingTriplet_optionValue second in
            if x <= s then
              increasingTriplet_loop rest first (SOME x)
            else T)`;;

let increasingTriplet = new_definition
  `increasingTriplet (nums:int list) =
     if LENGTH nums < 3 then F
     else increasingTriplet_loop nums NONE NONE`;;

let increasingTriplet_zipIdxFrom =
  new_recursive_definition list_RECURSION
    `(increasingTriplet_zipIdxFrom
        (start:num) ([]:int list) = []) /\
     (!x:int. !rest:int list. !start:num.
        increasingTriplet_zipIdxFrom start (CONS x rest) =
        CONS (x,start)
          (increasingTriplet_zipIdxFrom (SUC start) rest))`;;

let increasingTriplet_zipIdx = new_definition
  `increasingTriplet_zipIdx (nums:int list) =
     increasingTriplet_zipIdxFrom 0 nums`;;

let increasingTriplet_postcond = new_definition
  `increasingTriplet_postcond
      (nums:int list) (result:bool) <=>
     let indexed = increasingTriplet_zipIdx nums in
     (result
      ==> EX
            (\xi:int#num.
               EX
                 (\yj:int#num.
                    EX
                      (\zk:int#num.
                         SND xi < SND yj /\
                         SND yj < SND zk /\
                         FST xi < FST yj /\
                         FST yj < FST zk)
                      indexed)
                 indexed)
            indexed) /\
     (~result
      ==> ALL
            (\xi:int#num.
               ALL
                 (\yj:int#num.
                    ALL
                      (\zk:int#num.
                         SND yj <= SND xi \/
                         SND zk <= SND yj \/
                         FST yj <= FST xi \/
                         FST zk <= FST yj)
                      indexed)
                 indexed)
            indexed)`;;

let increasingTriplet_spec_satisfied =
  `!nums:int list.
     increasingTriplet_precond nums
     ==> increasingTriplet_postcond nums (increasingTriplet nums)`;;
