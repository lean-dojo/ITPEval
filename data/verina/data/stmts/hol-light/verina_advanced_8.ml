(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_8,
  catalog title "canCompleteCircuit": an executable greedy scan returns the
  least gas-station index from which every circular prefix has nonnegative
  fuel, or -1 when no start works, with its precondition and full correctness
  contract. This file contains no proof.
*)

let canCompleteCircuit_precond = new_definition
  `canCompleteCircuit_precond
      (gas:int list) (cost:int list) <=>
     LENGTH gas > 0 /\
     LENGTH gas = LENGTH cost`;;

let canCompleteCircuit_sumFold =
  new_recursive_definition list_RECURSION
    `(!acc:int.
        canCompleteCircuit_sumFold ([]:int list) acc = acc) /\
     (!x:int. !xs:int list. !acc:int.
        canCompleteCircuit_sumFold (CONS x xs) acc =
        canCompleteCircuit_sumFold xs (acc + x))`;;

let canCompleteCircuit_zip =
  new_recursive_definition list_RECURSION
    `(!cost:int list.
        canCompleteCircuit_zip ([]:int list) cost =
        ([]:(int#int)list)) /\
     (!g:int. !gs:int list. !cost:int list.
        canCompleteCircuit_zip (CONS g gs) cost =
        if cost = [] then []
        else
          CONS (g,HD cost)
            (canCompleteCircuit_zip gs (TL cost)))`;;

let canCompleteCircuit_walk =
  new_recursive_definition list_RECURSION
    `(!i:num. !tank:int. !start:num.
        canCompleteCircuit_walk
          ([]:(int#int)list) i tank start =
        (&start:int)) /\
     (!station:int#int. !rest:(int#int)list.
      !i:num. !tank:int. !start:num.
        canCompleteCircuit_walk
          (CONS station rest) i tank start =
        let newTank =
          tank + FST station - SND station in
        if newTank < &0 then
          canCompleteCircuit_walk
            rest (i + 1) (&0:int) (i + 1)
        else
          canCompleteCircuit_walk
            rest (i + 1) newTank start)`;;

let canCompleteCircuit = new_definition
  `canCompleteCircuit
      (gas:int list) (cost:int list) =
     let totalGas =
       canCompleteCircuit_sumFold gas (&0:int) in
     let totalCost =
       canCompleteCircuit_sumFold cost (&0:int) in
     if totalGas < totalCost then (-- &1:int)
     else
       canCompleteCircuit_walk
         (canCompleteCircuit_zip gas cost)
         0 (&0:int) 0`;;

let canCompleteCircuit_range =
  new_recursive_definition num_RECURSION
    `(canCompleteCircuit_range 0 = []) /\
     (!n:num.
        canCompleteCircuit_range (SUC n) =
        APPEND
          (canCompleteCircuit_range n)
          (CONS n []))`;;

let canCompleteCircuit_balanceFold =
  new_recursive_definition list_RECURSION
    `(!gas:int list. !cost:int list. !start:num. !acc:int.
        canCompleteCircuit_balanceFold
          gas cost start acc ([]:num list) =
        acc) /\
     (!j:num. !js:num list.
      !gas:int list. !cost:int list. !start:num. !acc:int.
        canCompleteCircuit_balanceFold
          gas cost start acc (CONS j js) =
        let jdx =
          (start + j) MOD LENGTH gas in
        canCompleteCircuit_balanceFold
          gas cost start
          (acc + EL jdx gas - EL jdx cost)
          js)`;;

let canCompleteCircuit_valid = new_definition
  `canCompleteCircuit_valid
      (gas:int list) (cost:int list) (start:num) <=>
     ALL
       (\i:num.
          canCompleteCircuit_balanceFold
            gas cost start (&0:int)
            (canCompleteCircuit_range (i + 1))
          >= &0)
       (canCompleteCircuit_range (LENGTH gas))`;;

let canCompleteCircuit_intToNat = new_definition
  `canCompleteCircuit_intToNat (z:int) =
     if z < &0 then 0 else num_of_int z`;;

let canCompleteCircuit_postcond = new_definition
  `canCompleteCircuit_postcond
      (gas:int list) (cost:int list) (result:int) <=>
     result >= -- &1 /\
     (result = -- &1
      ==> ALL
            (\start:num.
               ~canCompleteCircuit_valid gas cost start)
            (canCompleteCircuit_range (LENGTH gas))) /\
     (result >= &0
      ==> result < &(LENGTH gas) /\
          canCompleteCircuit_valid
            gas cost
            (canCompleteCircuit_intToNat result) /\
          ALL
            (\start:num.
               ~canCompleteCircuit_valid gas cost start)
            (canCompleteCircuit_range
              (canCompleteCircuit_intToNat result)))`;;

let canCompleteCircuit_spec_satisfied =
  `!gas:int list. !cost:int list.
     canCompleteCircuit_precond gas cost
     ==> canCompleteCircuit_postcond
           gas cost (canCompleteCircuit gas cost)`;;
