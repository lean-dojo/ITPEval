(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_23,
  catalog title "isPowerOfTwo": a fuel-bounded executable repeated-halving
  test recognizes positive integer powers of two, together with its total
  correctness contract. This file contains no proof.
*)

let isPowerOfTwo_precond = new_definition
  `isPowerOfTwo_precond (n:int) <=> T`;;

let isPowerOfTwo_aux =
  new_recursive_definition num_RECURSION
    `(!m:num. isPowerOfTwo_aux 0 m = F) /\
     (!fuel:num. !m:num.
        isPowerOfTwo_aux (SUC fuel) m =
        if m = 1 then T
        else if ~(m MOD 2 = 0) then F
        else isPowerOfTwo_aux fuel (m DIV 2))`;;

let isPowerOfTwo = new_definition
  `isPowerOfTwo (n:int) =
     if n <= &0 then F
     else
       let magnitude = num_of_int (abs n) in
       isPowerOfTwo_aux magnitude magnitude`;;

let isPowerOfTwo_pow =
  new_recursive_definition num_RECURSION
    `(!base:int. isPowerOfTwo_pow 0 base = &1) /\
     (!exp:num. !base:int.
        isPowerOfTwo_pow (SUC exp) base =
        base * isPowerOfTwo_pow exp base)`;;

let isPowerOfTwo_postcond = new_definition
  `isPowerOfTwo_postcond (n:int) (result:bool) <=>
     if result then
       ?x:num. isPowerOfTwo_pow x (&2:int) = n /\ n > &0
     else
       ~(?x:num. isPowerOfTwo_pow x (&2:int) = n /\ n > &0)`;;

let isPowerOfTwo_spec_satisfied =
  `!n:int.
     isPowerOfTwo_precond n
     ==> isPowerOfTwo_postcond n (isPowerOfTwo n)`;;
