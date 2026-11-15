(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/there_and_back_again_Palindrome_palindrome_recqtvc: the recursive
  palindrome verification condition, covering its list cases, equality test,
  suffix result, and propagation of a non-palindrome witness. This file
  contains no proof.
*)

let statement =
 `let nth_opt =
    \(xs:A list) (i:int).
      if i < (&0:int) then (NONE:A option)
      else if num_of_int i < LENGTH xs then
        SOME (EL (num_of_int i) xs)
      else
        NONE in
  let pal =
    \(xs:A list) (n:int).
      !i:int.
        (&0:int) <= i /\ i < n
        ==> nth_opt xs i = nth_opt xs (n - (&1:int) - i) in
  let mismatch =
    \(xs:A list) (n:int).
      ?i:int.
        ((&0:int) <= i /\ i < n) /\
        ~(nth_opt xs i = nth_opt xs (n - (&1:int) - i)) in
  !eq:A->A->bool.
    (!a b:A. (eq a b <=> a = b))
    ==>
    !y x:A list.
      LENGTH y <= LENGTH x
      ==>
      if y = [] then
        (?x0:A list.
           LENGTH x0 = LENGTH y /\
           x = APPEND x0 x) /\
        pal x (&(LENGTH y):int)
      else
        let x1 = HD y in
        let x2 = TL y in
        if x2 = [] then
          if x = [] then
            F
          else
            let x3 = HD x in
            let x4 = TL x in
            (?x0:A list.
               LENGTH x0 = LENGTH y /\
               x = APPEND x0 x4) /\
            pal x (&(LENGTH y):int)
        else
          let x3 = HD x2 in
          let x4 = TL x2 in
          if x = [] then
            F
          else
            let x5 = HD x in
            let x6 = TL x in
            ((if x = [] then F else TL x = x6) /\
             LENGTH x4 <= LENGTH x6) /\
            (!o1:A list.
               ((?x0:A list.
                   LENGTH x0 = LENGTH x4 /\
                   x6 = APPEND x0 o1) /\
                pal x6 (&(LENGTH x4):int))
               ==>
               if o1 = [] then
                 F
               else
                 let x11 = HD o1 in
                 let xs = TL o1 in
                 (eq x5 x11 <=> x5 = x11)
                 ==>
                 if eq x5 x11 then
                   (?x0:A list.
                      LENGTH x0 = LENGTH y /\
                      x = APPEND x0 xs) /\
                   pal x (&(LENGTH y):int)
                 else
                   mismatch x (&(LENGTH y):int)) /\
            (mismatch x6 (&(LENGTH x4):int)
             ==> mismatch x (&(LENGTH y):int))`;;
