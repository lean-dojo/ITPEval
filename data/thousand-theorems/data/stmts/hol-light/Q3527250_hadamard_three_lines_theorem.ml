(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3527250,
  "Hadamard three-lines theorem": a bounded complex-differentiable function
  into an arbitrary complex normed space is bounded inside a vertical strip
  by the interpolation of its boundary-line supremum norms. This file
  contains no proof.
*)

let q3527250_output = open_out "/dev/null";;
let q3527250_formatter = Format.formatter_of_out_channel q3527250_output;;
let q3527250_previous_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file q3527250_formatter path);;
let q3527250_loaded =
  Toploop.use_file q3527250_formatter "Library/transc.ml";;
Hol_loader.file_loader := q3527250_previous_loader;;
Format.pp_print_flush q3527250_formatter ();;
close_out q3527250_output;;
if not q3527250_loaded then
  failwith "Unable to load transcendental library";;

let Q3527250_HADAMARD_THREE_LINES_THEOREM =
  `let czero = ((&0:real),(&0:real)) in
   let cone = ((&1:real),(&0:real)) in
   let cadd =
     \(z:real#real) (w:real#real).
       (FST z + FST w,SND z + SND w) in
   let cneg =
     \(z:real#real). (--(FST z),--(SND z)) in
   let csub =
     \(z:real#real) (w:real#real).
       (FST z - FST w,SND z - SND w) in
   let cmul =
     \(z:real#real) (w:real#real).
       (FST z * FST w - SND z * SND w,
        FST z * SND w + SND z * FST w) in
   let cnorm =
     \(z:real#real).
       sqrt(FST z pow 2 + SND z pow 2) in
   let is_complex_normed_space =
     \(zero:A) (add:A->A->A) (neg:A->A)
      (smul:(real#real)->A->A) (normA:A->real).
       (!x:A. add zero x = x) /\
       (!x:A. add x zero = x) /\
       (!x y:A. add x y = add y x) /\
       (!x y z:A. add (add x y) z = add x (add y z)) /\
       (!x:A. add (neg x) x = zero) /\
       (!x:A. add x (neg x) = zero) /\
       (!x:A. smul cone x = x) /\
       (!a b:real#real. !x:A.
          smul (cmul a b) x = smul a (smul b x)) /\
       (!a b:real#real. !x:A.
          smul (cadd a b) x = add (smul a x) (smul b x)) /\
       (!x:A. smul czero x = zero) /\
       (!a:real#real. !x y:A.
          smul a (add x y) = add (smul a x) (smul a y)) /\
       (!a:real#real. smul a zero = zero) /\
       normA zero = &0 /\
       (!x:A. &0 <= normA x) /\
       (!x:A. normA x = &0 <=> x = zero) /\
       (!x:A. normA (neg x) = normA x) /\
       (!a:real#real. !x:A.
          normA (smul a x) = cnorm a * normA x) /\
       (!x y:A. normA (add x y) <= normA x + normA y) in
   let subA =
     \(add:A->A->A) (neg:A->A) (x:A) (y:A). add x (neg y) in
   let vertical_closed_strip =
     \l u (z:real#real). l <= FST z /\ FST z <= u in
   let vertical_strip =
     \l u (z:real#real). l < FST z /\ FST z < u in
   let in_closure_of_vertical_strip =
     \(l:real) (u:real) (x:real#real).
       !epsilon:real.
         &0 < epsilon
         ==> ?w:real#real.
               vertical_strip l u w /\
               cnorm(csub w x) < epsilon in
   let continuous_on_strip_closure =
     \(add:A->A->A) (neg:A->A) (normA:A->real)
      (f:(real#real)->A) (l:real) (u:real).
       !x:real#real.
         in_closure_of_vertical_strip l u x
         ==> !epsilon:real.
               &0 < epsilon
               ==> ?delta:real.
                     &0 < delta /\
                     !y:real#real.
                       in_closure_of_vertical_strip l u y /\
                       cnorm(csub y x) < delta
                       ==> normA (subA add neg (f y) (f x)) < epsilon in
   let complex_differentiable_within_strip_at =
     \(add:A->A->A) (neg:A->A) (smul:(real#real)->A->A)
      (normA:A->real) (f:(real#real)->A)
      (l:real) (u:real) (x:real#real).
       ?derivative:A.
         !epsilon:real.
           &0 < epsilon
           ==> ?delta:real.
                 &0 < delta /\
                 !y:real#real.
                   vertical_strip l u y /\
                   cnorm(csub y x) < delta
                   ==> normA
                         (subA add neg
                           (subA add neg (f y) (f x))
                           (smul (csub y x) derivative))
                       <= epsilon * cnorm(csub y x) in
   let differentiable_on_open_strip =
     \(add:A->A->A) (neg:A->A) (smul:(real#real)->A->A)
      (normA:A->real) (f:(real#real)->A) (l:real) (u:real).
       !x:real#real.
         vertical_strip l u x
         ==> complex_differentiable_within_strip_at
               add neg smul normA f l u x in
   let diff_cont_on_cl =
     \(add:A->A->A) (neg:A->A) (smul:(real#real)->A->A)
      (normA:A->real) (f:(real#real)->A) (l:real) (u:real).
       differentiable_on_open_strip add neg smul normA f l u /\
       continuous_on_strip_closure add neg normA f l u in
   let bounded_on_closed_strip =
     \(normA:A->real) (f:(real#real)->A) (l:real) (u:real).
       ?bound:real.
         !x:real#real.
           vertical_closed_strip l u x ==> normA (f x) <= bound in
   let sSupNormIm =
     \(normA:A->real) (f:(real#real)->A) (x:real).
       sup {r:real |
              ?w:real#real. FST w = x /\ r = normA (f w)} in
   let interpNorm =
     \(normA:A->real) (f:(real#real)->A)
      (l:real) (u:real) (z:real#real).
       let ml = sSupNormIm normA f l in
       let mu = sSupNormIm normA f u in
       let t = (FST z - l) / (u - l) in
       if ml = &0 \/ mu = &0
       then &0
       else exp((&1 - t) * ln ml) * exp(t * ln mu) in
   !(zero:A) (add:A->A->A) (neg:A->A)
    (smul:(real#real)->A->A) (normA:A->real)
    (l:real) (u:real) (f:(real#real)->A) (z:real#real).
      is_complex_normed_space zero add neg smul normA /\
      l < u /\
      vertical_closed_strip l u z /\
      diff_cont_on_cl add neg smul normA f l u /\
      bounded_on_closed_strip normA f l u
      ==> normA (f z) <= interpNorm normA f l u z`;;
