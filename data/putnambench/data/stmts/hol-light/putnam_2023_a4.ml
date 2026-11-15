(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2023_a4
  (putnambench__hol-light__putnam_2023_a4): density in real three-space of
  the integer span of the twelve normalized vertices of a regular
  icosahedron. This file contains no proof.
*)

let vectors_output = open_out "/dev/null";;
let vectors_formatter = Format.formatter_of_out_channel vectors_output;;
let vectors_loaded =
  Toploop.use_file vectors_formatter "Multivariate/vectors.ml";;
Format.pp_print_flush vectors_formatter ();;
close_out vectors_output;;
if not vectors_loaded then failwith "failed to load Multivariate/vectors.ml";;

let statement =
  `let phi = (&1 + sqrt (&5)) / &2 in
   let scale = sqrt (&1 + phi pow 2) in
   let vertex =
     \i:num.
       if i = 1 then
         (lambda j. if j = 1 then &1 else if j = 2 then phi else &0):real^3
       else if i = 2 then
         (lambda j. if j = 1 then -- &1 else if j = 2 then phi else &0):real^3
       else if i = 3 then
         (lambda j. if j = 1 then &1 else if j = 2 then --phi else &0):real^3
       else if i = 4 then
         (lambda j. if j = 1 then -- &1 else if j = 2 then --phi else &0):real^3
       else if i = 5 then
         (lambda j. if j = 1 then phi else if j = 2 then &0 else &1):real^3
       else if i = 6 then
         (lambda j. if j = 1 then phi else if j = 2 then &0 else -- &1):real^3
       else if i = 7 then
         (lambda j. if j = 1 then --phi else if j = 2 then &0 else &1):real^3
       else if i = 8 then
         (lambda j. if j = 1 then --phi else if j = 2 then &0 else -- &1):real^3
       else if i = 9 then
         (lambda j. if j = 1 then &0 else if j = 2 then &1 else phi):real^3
       else if i = 10 then
         (lambda j. if j = 1 then &0 else if j = 2 then -- &1 else phi):real^3
       else if i = 11 then
         (lambda j. if j = 1 then &0 else if j = 2 then &1 else --phi):real^3
       else
         (lambda j. if j = 1 then &0 else if j = 2 then -- &1 else --phi):real^3 in
   !(v:real^3^12).
     (?g:real^3->real^3.
        linear g /\
        (!x:real^3. norm (g x) = norm x) /\
        (!y:real^3. ?x:real^3. g x = y) /\
        (!i:num.
           i IN 1..12
           ==> g (v$i) = inv scale % vertex i))
     ==>
     !w:real^3. !e:real.
       &0 < e
       ==>
       ?a:int^12.
         norm
           (vsum (1..12)
              (\i:num. real_of_int (a$i) % v$i) -
            w) < e`;;
