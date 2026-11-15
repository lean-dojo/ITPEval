(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2021_b3
  (putnambench__hol-light__putnam_2021_b3): a zero disk integral for the
  angular derivative of every twice continuously differentiable real-valued
  function on the plane. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let point =
     \(x:real) (y:real).
       (lambda i. if i = 1 then x else y):real^2 in
   let xrepl =
     \(x:real^2) (i:num) (t:real).
       (lambda k. if k = i then t else x$k):real^2 in
   let has_derivative_at =
     \(f:real->real) (d:real) (x:real).
       !e:real.
         &0 < e
         ==> ?delta:real.
               &0 < delta /\
               !y:real.
                 &0 < abs (y - x) /\ abs (y - x) < delta
                 ==> abs ((f y - f x) / (y - x) - d) < e in
   let continuous_on_plane =
     \(f:real^2->real).
       !x:real^2. !e:real.
         &0 < e
         ==> ?delta:real.
               &0 < delta /\
               !y:real^2.
                 sqrt
                   ((y$1 - x$1) pow 2 + (y$2 - x$2) pow 2) < delta
                 ==> abs (f y - f x) < e in
   let partial =
     \(h:real^2->real) (i:num) (x:real^2).
       @d:real.
         has_derivative_at
           (\t:real. h (xrepl x i t)) d (x$i) in
   let second_partial =
     \(h:real^2->real) (i:num) (j:num) (x:real^2).
       @d:real.
         has_derivative_at
           (\t:real. partial h i (xrepl x j t)) d (x$j) in
   let twice_continuously_differentiable =
     \(h:real^2->real).
       (!i:num.
          1 <= i /\ i <= 2
          ==>
          (!x:real^2.
             has_derivative_at
               (\t:real. h (xrepl x i t))
               (partial h i x) (x$i)) /\
          continuous_on_plane (partial h i)) /\
       (!i j:num.
          1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
          ==>
          (!x:real^2.
             has_derivative_at
               (\t:real. partial h i (xrepl x j t))
               (second_partial h i j x) (x$j)) /\
          continuous_on_plane (second_partial h i j)) in
   let rho =
     \(h:real^2->real) (x:real^2).
       x$2 * partial h 1 x - x$1 * partial h 2 x in
   let disk_integral =
     \(h:real^2->real) (c:real^2) (r:real).
       integral(c$1 - r,c$1 + r)
         (\x:real.
            integral
              (c$2 - sqrt (r pow 2 - (x - c$1) pow 2),
               c$2 + sqrt (r pow 2 - (x - c$1) pow 2))
              (\y:real. rho h (point x y))) in
   let putnam_2021_b3_solution = T in
   ((!h:real^2->real.
       twice_continuously_differentiable h
       ==>
       !d r:real.
         &0 < d /\ &0 < r /\ r < d
         ==>
         ?c:real^2.
           sqrt ((c$1) pow 2 + (c$2) pow 2) = d /\
           disk_integral h c r = &0)
    <=>
    putnam_2021_b3_solution)`;;
