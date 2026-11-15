(*
  Statement-only formalization of Thousand Theorems corpus artifact Q5171652,
  "Corners theorem": a sufficiently dense finite subset of [0,n) x [0,n)
  contains a nontrivial additive corner once n meets the explicit
  regularity-and-removal bound. This file contains no proof.
*)

needs "Library/transc.ml";;

let q5171652_output = open_out "/dev/null";;
let q5171652_formatter =
  Format.formatter_of_out_channel q5171652_output;;
let q5171652_previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file q5171652_formatter path);;
let q5171652_iter_loaded =
  Toploop.use_file q5171652_formatter "Library/iter.ml";;
Hol_loader.file_loader := q5171652_previous_file_loader;;
Format.pp_print_flush q5171652_formatter ();;
close_out q5171652_output;;
if not q5171652_iter_loaded then
  failwith "failed to load Library/iter.ml";;

let Q5171652_CORNERS_THEOREM =
  `let nat_floor =
     \x:real.
       if x < &0 then 0
       else @n:num. &n <= x /\ x < &(n + 1) in
   let nat_ceiling =
     \x:real.
       @n:num.
         x <= &n /\
         (!m:num. x <= &m ==> n <= m) in
   let step_bound =
     \m:num. m * 4 EXP m in
   let initial_bound =
     \(e:real) (l:num).
       MAX 7
         (MAX l
           (nat_floor
             (ln (&100 / e pow 5) / ln (&4)) +
            1)) in
   let regularity_bound =
     \(e:real) (l:num).
       let q =
         ITER (nat_floor (&4 / e pow 5))
           step_bound (initial_bound e l) in
       q * 16 EXP q in
   let triangle_removal_bound =
     \e:real.
       min
         (inv
           (&(2 * nat_ceiling (&4 / e) EXP 3)))
         ((&1 - min (&1) e / &4) *
          (e /
           (&16 *
            &(regularity_bound
                (e / &8)
                (nat_ceiling (&4 / e))))) pow 3) in
   let corners_bound =
     \e:real.
       nat_floor
         (inv (triangle_removal_bound (e / &9) * &27)) + 1 in
   let corner_free =
     \A:(num#num)->bool.
       !x1 y1 x2 y2:num.
         (x1,y1) IN A /\
         (x1,y2) IN A /\
         (x2,y1) IN A /\
         x1 + y2 = x2 + y1
         ==> x1 = x2 in
   !e:real. !n:num. !A:(num#num)->bool.
     &0 < e /\
     corners_bound (e / &9) <= n /\
     FINITE A /\
     (!x y:num. (x,y) IN A ==> x < n /\ y < n) /\
     e * (&n pow 2) <= &(CARD A)
     ==> ~(corner_free A)`;;
