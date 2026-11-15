(*
  Statement-only formalization of PutnamBench artifact putnam_1965_a1:
  a nondegenerate real-plane triangle satisfying the stated external
  angle-bisector, collinearity, and equal-distance conditions has angle CAB
  equal to pi / 15. This file contains no proof.
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
     \(p:real#real) (q:real#real).
       (FST p - FST q,SND p - SND q) in
   let dot =
     \(u:real#real) (v:real#real).
       FST u * FST v + SND u * SND v in
   let norm =
     \(u:real#real).
       sqrt (dot u u) in
   let vangle =
     \(u:real#real) (v:real#real).
       if u = (&0,&0) \/ v = (&0,&0) then pi / &2
       else acs (dot u v / (norm u * norm v)) in
   let angle =
     \(a:real#real) (b:real#real) (c:real#real).
       vangle (vsub a b) (vsub c b) in
   let collinear3 =
     \(a:real#real) (b:real#real) (c:real#real).
       (FST a - FST b) * (SND c - SND b) =
       (SND a - SND b) * (FST c - FST b) in
   let distance =
     \(p:real#real) (q:real#real).
       norm (vsub p q) in
   let putnam_1965_a1_solution = pi / &15 in
   !A B C X Y:real#real.
     ~(collinear3 A B C) /\
     angle C A B < angle B C A /\
     angle B C A < pi / &2 /\
     pi / &2 < angle A B C /\
     collinear3 X B C /\
     angle X A B = (pi - angle C A B) / &2 /\
     distance A X = distance A B /\
     collinear3 Y C A /\
     angle Y B C = (pi - angle A B C) / &2 /\
     distance B Y = distance A B
     ==> angle C A B = putnam_1965_a1_solution`;;
