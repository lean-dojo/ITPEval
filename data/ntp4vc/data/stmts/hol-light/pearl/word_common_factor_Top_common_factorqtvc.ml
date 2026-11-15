(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/word_common_factor_Top_common_factorqtvc: the verification condition
  for two commuting words to have nonnegative powers of a common word,
  including the recursive-call descent obligations. This file contains no
  proof.
*)

let ntp4vc_common_factor_drop =
  new_recursive_definition num_RECURSION
   `(!xs:A list. ntp4vc_common_factor_drop 0 xs = xs) /\
    (!n:num.
     !xs:A list.
       ntp4vc_common_factor_drop (SUC n) xs =
       if xs = [] then []
       else ntp4vc_common_factor_drop n (TL xs))`;;

let statement =
 `!power:A list->int->A list.
    (!n:int.
     !w:A list.
       (&0:int) <= n
       ==>
       (if n = (&0:int)
        then power w n = []
        else power w n = APPEND w (power w (n - (&1:int)))))
    ==>
    !a b:A list.
      APPEND a b = APPEND b a
      ==>
      let o1 = (&(LENGTH a):int) in
      (~(o1 = (&0:int))
       ==>
       ~((&(LENGTH b):int) = (&0:int))
       ==>
       (if LENGTH a <= LENGTH b then
          let o2 = (&(LENGTH a):int) in
          ((&0:int) <= o2 /\ o2 <= (&(LENGTH b):int)) /\
          (let c = ntp4vc_common_factor_drop (num_of_int o2) b in
           b = APPEND a c /\
           (b = APPEND a c
            ==>
            (((&0:int) <= (&(LENGTH b):int) /\
              LENGTH c < LENGTH b) /\
             APPEND a c = APPEND c a)))
        else
          ((((&0:int) <= (&(LENGTH a):int) /\
             LENGTH b < LENGTH a) \/
            (LENGTH a = LENGTH b /\
             (&0:int) <= (&(LENGTH b):int) /\
             LENGTH a < LENGTH b)) /\
           APPEND b a = APPEND a b))) /\
      (!w:A list.
       !ka kb:int.
         (if o1 = (&0:int) then
            w = b /\ ka = (&0:int) /\ kb = (&1:int)
          else if (&(LENGTH b):int) = (&0:int) then
            w = a /\ ka = (&1:int) /\ kb = (&0:int)
          else if LENGTH a <= LENGTH b then
            let c = ntp4vc_common_factor_drop (LENGTH a) b in
            b = APPEND a c /\
            (?kb1:int.
               (((&0:int) <= ka /\ a = power w ka) /\
                (&0:int) <= kb1 /\ c = power w kb1) /\
               kb = ka + kb1)
          else
            ((&0:int) <= kb /\ b = power w kb) /\
            (&0:int) <= ka /\ a = power w ka)
         ==>
         (((&0:int) <= ka /\ a = power w ka) /\
          (&0:int) <= kb /\ b = power w kb))`;;
