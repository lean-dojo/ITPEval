(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2019_b4
  (putnambench__hol-light__putnam_2019_b4): the common greatest lower bound
  of a mixed finite difference for twice continuously differentiable real
  functions satisfying two partial differential equations on the quadrant.
  This file contains no proof.
*)

let transc_output = open_out "/dev/null";;
let transc_formatter = Format.formatter_of_out_channel transc_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file transc_formatter path);;
let transc_loaded =
  Toploop.use_file transc_formatter "Library/transc.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush transc_formatter ();;
close_out transc_output;;
if not transc_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let pair =
     \x y:real.
       (lambda i. if i = 1 then x else y):real^2 in
   let xrepl =
     \(x:real^2) (i:num) (t:real).
       (lambda k. if k = i then t else x$k):real^2 in
   let has_derivative_at =
     \(h:real->real) (d:real) (a:real).
       !e:real.
         &0 < e
         ==> ?delta:real.
               &0 < delta /\
               !b:real.
                 &0 < abs (b - a) /\ abs (b - a) < delta
                 ==> abs ((h b - h a) / (b - a) - d) < e in
   let partial =
     \(h:real^2->real) (i:num) (x:real^2).
       @d:real.
         has_derivative_at
           (\t:real. h (xrepl x i t)) d (x$i) in
   let in_quadrant =
     \x:real^2. &1 <= x$1 /\ &1 <= x$2 in
   let continuous_on_quadrant =
     \(h:real^2->real).
       !x:real^2.
         in_quadrant x
         ==> !e:real.
               &0 < e
               ==> ?delta:real.
                     &0 < delta /\
                     !y:real^2.
                       in_quadrant y /\
                       abs (y$1 - x$1) < delta /\
                       abs (y$2 - x$2) < delta
                       ==> abs (h y - h x) < e in
   let contdiff2_on_quadrant =
     \(h:real^2->real).
       continuous_on_quadrant h /\
       (!i:num.
          1 <= i /\ i <= 2
          ==>
          (!x:real^2.
             in_quadrant x
             ==> has_derivative_at
                   (\t:real. h (xrepl x i t))
                   (partial h i x) (x$i)) /\
          continuous_on_quadrant (partial h i)) /\
       (!i j:num.
          1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
          ==>
          (!x:real^2.
             in_quadrant x
             ==> has_derivative_at
                   (\t:real. partial h i (xrepl x j t))
                   (partial (partial h i) j x) (x$j)) /\
          continuous_on_quadrant (partial (partial h i) j)) in
   let objective =
     \(f:real^2->real) (s:real).
       f (pair (s + &1) (s + &1)) -
       f (pair (s + &1) s) -
       f (pair s (s + &1)) +
       f (pair s s) in
   let lower_bound =
     \(f:real^2->real) (m:real).
       !s:real. &1 <= s ==> m <= objective f s in
   let putnam_2019_b4_solution =
     &2 * ln (&2) - &1 / &2 in
   !f:real^2->real.
     contdiff2_on_quadrant f /\
     (!x y:real.
        &1 <= x /\ &1 <= y
        ==>
        x * partial f 1 (pair x y) +
        y * partial f 2 (pair x y) =
        x * y * ln (x * y)) /\
     (!x y:real.
        &1 <= x /\ &1 <= y
        ==>
        x pow 2 * partial (partial f 1) 1 (pair x y) +
        y pow 2 * partial (partial f 2) 2 (pair x y) =
        x * y)
     ==>
     lower_bound f putnam_2019_b4_solution /\
     (!m:real.
        lower_bound f m ==> m <= putnam_2019_b4_solution)`;;
