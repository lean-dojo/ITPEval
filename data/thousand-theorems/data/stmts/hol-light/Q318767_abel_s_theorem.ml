(*
  Statement-only formalization of Thousand Theorems corpus artifact Q318767,
  (thousand-theorems__hol-light__Q318767), "Abel's theorem": if the
  coefficient series converges at one, its complex power series tends to that
  sum within every positive Stolz cone, and its real power series tends to the
  sum from the left. This file contains no proof.
*)

let q318767_output = open_out "/dev/null";;
let q318767_formatter = Format.formatter_of_out_channel q318767_output;;
let q318767_previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file q318767_formatter path);;
let q318767_complex_loaded =
  Toploop.use_file q318767_formatter "Complex/complexnumbers.ml";;
Hol_loader.file_loader := q318767_previous_file_loader;;
Format.pp_print_flush q318767_formatter ();;
close_out q318767_output;;
if not q318767_complex_loaded then
  failwith "failed to load Complex/complexnumbers.ml";;

let Q318767_ABEL_S_THEOREM =
  `let complex_partial_sum =
     \(f:num->complex) (n:num).
       complex
         (sum(0,n) (\i:num. Re(f i)),
          sum(0,n) (\i:num. Im(f i))) in
   let complex_tends =
     \(u:num->complex) (l:complex).
       !e:real.
         &0 < e
         ==> ?N:num.
               !n:num.
                 N <= n ==> norm(u n - l) < e in
   let complex_sums =
     \(f:num->complex) (l:complex).
       complex_tends (\n:num. complex_partial_sum f n) l in
   let complex_tsum =
     \(f:num->complex).
       if ?l:complex. complex_sums f l
       then @l:complex. complex_sums f l
       else Cx(&0) in
   let real_partial_sum =
     \(f:num->real) (n:num). sum(0,n) f in
   let real_tends =
     \(u:num->real) (l:real).
       !e:real.
         &0 < e
         ==> ?N:num.
               !n:num.
                 N <= n ==> abs(u n - l) < e in
   let real_sums =
     \(f:num->real) (l:real).
       real_tends (\n:num. real_partial_sum f n) l in
   let real_tsum =
     \(f:num->real).
       if ?l:real. real_sums f l
       then @l:real. real_sums f l
       else &0 in
   let complex_tends_within =
     \(g:complex->complex) (l:complex) (a:complex)
      (region:complex->bool).
       !e:real.
         &0 < e
         ==> ?d:real.
               &0 < d /\
               !z:complex.
                 region z /\ norm(z - a) < d
                 ==> norm(g z - l) < e in
   let real_tends_from_left_at_one =
     \(g:real->real) (l:real).
       !e:real.
         &0 < e
         ==> ?d:real.
               &0 < d /\
               !x:real.
                 x < &1 /\ abs(x - &1) < d
                 ==> abs(g x - l) < e in
   let stolz_cone =
     \(s:real) (z:complex).
       abs(Im z) < s * (&1 - Re z) in
   ((!f:num->complex. !l:complex. !s:real.
       complex_sums f l /\ &0 < s
       ==>
       complex_tends_within
         (\z:complex.
            complex_tsum (\n:num. f n * z pow n))
         l (Cx(&1)) (stolz_cone s)) /\
    (!f:num->real. !l:real.
       real_sums f l
       ==>
       real_tends_from_left_at_one
         (\x:real. real_tsum (\n:num. f n * x pow n))
         l))`;;
