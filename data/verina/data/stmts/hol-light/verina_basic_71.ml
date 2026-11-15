(*
  Statement-only formalization of VERINA corpus artifact verina_basic_71
  (verina__hol-light__verina_basic_71), catalog title
  "LongestCommonPrefix": an executable indexed scan returns the longest
  common prefix of two Unicode character lists, together with its total
  precondition and exact prefix-maximality correctness contract. This file
  contains no proof.
*)

let LongestCommonPrefix_validChar = new_definition
  `LongestCommonPrefix_validChar (c:num) <=>
     c < 55296 \/ (57343 < c /\ c < 1114112)`;;

let LongestCommonPrefix_string = new_definition
  `LongestCommonPrefix_string (s:num list) <=>
     ALL LongestCommonPrefix_validChar s`;;

let LongestCommonPrefix_precond = new_definition
  `LongestCommonPrefix_precond
      (str1:num list) (str2:num list) <=> T`;;

let LongestCommonPrefix_minLength = new_definition
  `LongestCommonPrefix_minLength
      (str1:num list) (str2:num list) =
     MIN (LENGTH str1) (LENGTH str2)`;;

let LongestCommonPrefix_getOption = new_definition
  `LongestCommonPrefix_getOption
      (s:num list) (idx:num) =
     if idx < LENGTH s then SOME (EL idx s)
     else (NONE:num option)`;;

let LongestCommonPrefix_optionValue =
  new_recursive_definition option_RECURSION
    `(LongestCommonPrefix_optionValue
        (NONE:num option) = 0) /\
     (!c:num.
        LongestCommonPrefix_optionValue (SOME c) = c)`;;

let LongestCommonPrefix_auxFuel =
  new_recursive_definition num_RECURSION
    `(!str1:num list. !str2:num list. !idx:num. !acc:num list.
        LongestCommonPrefix_auxFuel
          0 str1 str2 idx acc = acc) /\
     (!fuel:num. !str1:num list. !str2:num list.
      !idx:num. !acc:num list.
        LongestCommonPrefix_auxFuel
          (SUC fuel) str1 str2 idx acc =
        let minLength =
          LongestCommonPrefix_minLength str1 str2 in
        if idx < minLength then
          let c1Option =
            LongestCommonPrefix_getOption str1 idx in
          let c2Option =
            LongestCommonPrefix_getOption str2 idx in
          if c1Option = NONE \/ c2Option = NONE then
            acc
          else
            let c1 =
              LongestCommonPrefix_optionValue c1Option in
            let c2 =
              LongestCommonPrefix_optionValue c2Option in
            if ~(c1 = c2) then
              acc
            else
              LongestCommonPrefix_auxFuel
                fuel str1 str2 (idx + 1)
                (APPEND acc (CONS c1 []))
        else
          acc)`;;

let LongestCommonPrefix_aux = new_definition
  `LongestCommonPrefix_aux
      (str1:num list) (str2:num list)
      (idx:num) (acc:num list) =
     LongestCommonPrefix_auxFuel
       (SUC
         (LongestCommonPrefix_minLength str1 str2 - idx))
       str1 str2 idx acc`;;

let LongestCommonPrefix = new_definition
  `LongestCommonPrefix
      (str1:num list) (str2:num list) =
     LongestCommonPrefix_aux str1 str2 0 []`;;

let LongestCommonPrefix_take =
  new_recursive_definition num_RECURSION
    `(!s:num list.
        LongestCommonPrefix_take 0 s = []) /\
     (!n:num. !s:num list.
        LongestCommonPrefix_take (SUC n) s =
        if s = [] then
          []
        else
          CONS (HD s)
            (LongestCommonPrefix_take n (TL s)))`;;

let LongestCommonPrefix_postcond = new_definition
  `LongestCommonPrefix_postcond
      (str1:num list) (str2:num list)
      (result:num list) <=>
     LENGTH result <= LENGTH str1 /\
     result =
       LongestCommonPrefix_take (LENGTH result) str1 /\
     LENGTH result <= LENGTH str2 /\
     result =
       LongestCommonPrefix_take (LENGTH result) str2 /\
     (LENGTH result = LENGTH str1 \/
      LENGTH result = LENGTH str2 \/
      ~(LongestCommonPrefix_getOption
          str1 (LENGTH result) =
        LongestCommonPrefix_getOption
          str2 (LENGTH result)))`;;

let LongestCommonPrefix_spec_satisfied =
  `!str1:num list. !str2:num list.
     LongestCommonPrefix_string str1
     ==> LongestCommonPrefix_string str2
     ==> LongestCommonPrefix_precond str1 str2
     ==> LongestCommonPrefix_postcond
           str1 str2
           (LongestCommonPrefix str1 str2)`;;
