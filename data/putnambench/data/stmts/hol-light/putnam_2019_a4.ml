(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2019_a4
  (putnambench__hol-light__putnam_2019_a4): the negative answer to whether a
  continuous real-valued function on three-space with zero surface integral
  over every unit sphere must vanish identically. This file contains no proof.
*)

let transc_output = open_out "/dev/null";;
let transc_formatter = Format.formatter_of_out_channel transc_output;;
let previous_file_loader = !Hol_loader.file_loader;;
let previous_verbose = !verbose;;
let previous_type_invention_warning = !type_invention_warning;;
verbose := false;;
type_invention_warning := false;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file transc_formatter path);;
let transc_loaded =
  Toploop.use_file transc_formatter "Library/transc.ml";;
Hol_loader.file_loader := previous_file_loader;;
verbose := previous_verbose;;
type_invention_warning := previous_type_invention_warning;;
Format.pp_print_flush transc_formatter ();;
close_out transc_output;;
if not transc_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let continuous =
     \(f:real^3->real).
       !x:real^3. !e:real.
         &0 < e
         ==> ?d:real.
               &0 < d /\
               !y:real^3.
                 (y$1 - x$1) pow 2 +
                 (y$2 - x$2) pow 2 +
                 (y$3 - x$3) pow 2 < d pow 2
                 ==> abs (f y - f x) < e in
   let sphere_point =
     \(c:real^3) (u:real) (v:real).
       (lambda i.
          if i = 1 then c$1 + sin u * cos v
          else if i = 2 then c$2 + sin u * sin v
          else c$3 + cos u):real^3 in
   let unit_sphere_surface_integral =
     \(f:real^3->real) (c:real^3).
       integral(&0,pi)
         (\u:real.
            integral(&0,&2 * pi)
              (\v:real. f (sphere_point c u v) * sin u)) in
   ((!f:real^3->real.
       continuous f /\
       (!c:real^3. unit_sphere_surface_integral f c = &0)
       ==> f = (\x:real^3. &0))
    <=> F)`;;
