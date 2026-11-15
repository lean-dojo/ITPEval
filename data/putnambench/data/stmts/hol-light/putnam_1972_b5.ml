(*
  Statement-only formalization of PutnamBench artifact putnam_1972_b5:
  a nonplanar quadrilateral in three-dimensional Euclidean space with two
  pairs of equal opposite angles has the corresponding opposite side lengths
  equal. This file contains no proof.
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
  `let vsub =
     \(p:real#(real#real)) (q:real#(real#real)).
       (FST p - FST q,
        (FST (SND p) - FST (SND q),SND (SND p) - SND (SND q))) in
   let vadd =
     \(u:real#(real#real)) (v:real#(real#real)).
       (FST u + FST v,
        (FST (SND u) + FST (SND v),SND (SND u) + SND (SND v))) in
   let smul =
     \c (u:real#(real#real)).
       (c * FST u,(c * FST (SND u),c * SND (SND u))) in
   let dot =
     \(u:real#(real#real)) (v:real#(real#real)).
       FST u * FST v +
       FST (SND u) * FST (SND v) +
       SND (SND u) * SND (SND v) in
   let norm =
     \(u:real#(real#real)).
       sqrt (dot u u) in
   let vangle =
     \(u:real#(real#real)) (v:real#(real#real)).
       if u = (&0,(&0,&0)) \/ v = (&0,(&0,&0)) then pi / &2
       else acs (dot u v / (norm u * norm v)) in
   let angle =
     \(a:real#(real#real)) (b:real#(real#real))
      (c:real#(real#real)).
       vangle (vsub a b) (vsub c b) in
   let distance =
     \(p:real#(real#real)) (q:real#(real#real)).
       norm (vsub p q) in
   let coplanar =
     \(s:(real#(real#real))->bool).
       ?u v:real#(real#real).
         !x y. x IN s /\ y IN s
               ==> ?c d:real.
                     vsub x y = vadd (smul c u) (smul d v) in
   !A B C D:real#(real#real).
     ~(coplanar {A,B,C,D}) /\
     angle A B C = angle C D A /\
     angle B C D = angle D A B
     ==> distance A B = distance C D /\
         distance B C = distance D A`;;
