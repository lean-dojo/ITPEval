(*
  Statement-only formalization of Thousand Theorems corpus artifact Q834025
  (thousand-theorems__hol-light__Q834025), "Cauchy integral theorem": the
  Cauchy integral formula on a circle for a complex-valued function continuous
  on the closed disc and complex differentiable in its interior outside a
  countable set. This file contains no proof.
*)

let q834025_output = open_out "/dev/null";;
let q834025_formatter = Format.formatter_of_out_channel q834025_output;;
let q834025_previous_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file q834025_formatter path);;
let q834025_loaded =
  Toploop.use_file q834025_formatter "Library/transc.ml";;
Hol_loader.file_loader := q834025_previous_loader;;
Format.pp_print_flush q834025_formatter ();;
close_out q834025_output;;
if not q834025_loaded then failwith "Unable to load transcendental library";;

let Q834025_CAUCHY_INTEGRAL_THEOREM =
  `let cadd =
       \(z:real#real) (u:real#real).
         (FST z + FST u,SND z + SND u) in
   let csub =
       \(z:real#real) (u:real#real).
         (FST z - FST u,SND z - SND u) in
   let cmul =
       \(z:real#real) (u:real#real).
         (FST z * FST u - SND z * SND u,
          FST z * SND u + SND z * FST u) in
   let cinv =
       \(z:real#real).
         let q = FST z * FST z + SND z * SND z in
         (FST z / q,--(SND z) / q) in
   let cdiv =
       \(z:real#real) (u:real#real).
         cmul z (cinv u) in
   let cnorm =
       \(z:real#real).
         sqrt(FST z * FST z + SND z * SND z) in
   let open_disc =
       \(c:real#real) (R:real) (z:real#real).
         cnorm (csub z c) < R in
   let closed_disc =
       \(c:real#real) (R:real) (z:real#real).
         cnorm (csub z c) <= R in
   let continuous_on_closed_disc =
       \(c:real#real) (R:real) (f:(real#real)->real#real).
         !x:real#real.
           closed_disc c R x
           ==> !epsilon:real.
                 &0 < epsilon
                 ==> ?delta:real.
                       &0 < delta /\
                       !y:real#real.
                         closed_disc c R y /\
                         cnorm (csub y x) < delta
                         ==> cnorm (csub (f y) (f x)) < epsilon in
   let complex_differentiable_at =
       \(f:(real#real)->real#real) (x:real#real).
         ?d:real#real.
           !epsilon:real.
             &0 < epsilon
             ==> ?delta:real.
                   &0 < delta /\
                   !h:real#real.
                     cnorm h < delta
                     ==> cnorm
                           (csub
                             (csub (f (cadd x h)) (f x))
                             (cmul d h))
                         <= epsilon * cnorm h in
   let circle =
       \(c:real#real) (R:real) (theta:real).
         cadd c (R * cos theta,R * sin theta) in
   let circle_derivative =
       \(R:real) (theta:real).
         (--(R * sin theta),R * cos theta) in
   let cauchy_integrand =
       \(c:real#real) (R:real) (w:real#real)
        (f:(real#real)->real#real) (theta:real).
         cmul
           (cdiv (f (circle c R theta))
                 (csub (circle c R theta) w))
           (circle_derivative R theta) in
   let circle_integral =
       \(c:real#real) (R:real) (w:real#real)
        (f:(real#real)->real#real).
         (integral(&0,&2 * pi)
            (\theta. FST (cauchy_integrand c R w f theta)),
          integral(&0,&2 * pi)
            (\theta. SND (cauchy_integrand c R w f theta))) in
   !(R:real) (c:real#real) (w:real#real)
     (s:(real#real)->bool) (f:(real#real)->real#real).
       COUNTABLE s /\
       open_disc c R w /\
       continuous_on_closed_disc c R f /\
       (!z:real#real.
          open_disc c R z /\ ~(z IN s)
          ==> complex_differentiable_at f z)
       ==> circle_integral c R w f =
           cmul (cmul (&2 * pi,&0) (&0,&1)) (f w)`;;
