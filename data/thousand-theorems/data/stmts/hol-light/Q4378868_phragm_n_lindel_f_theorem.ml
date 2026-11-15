(*
  Statement-only formalization of Thousand Theorems corpus artifact Q4378868,
  "Phragmén–Lindelöf theorem": a complex-differentiable function into an
  arbitrary complex normed space, with subcritical double-exponential growth
  on a horizontal strip and a common norm bound on both boundary lines, obeys
  that bound throughout the closed strip. This file contains no proof.
*)

let q4378868_output = open_out "/dev/null";;
let q4378868_formatter = Format.formatter_of_out_channel q4378868_output;;
let q4378868_previous_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file q4378868_formatter path);;
let q4378868_loaded =
  Toploop.use_file q4378868_formatter "Library/transc.ml";;
Hol_loader.file_loader := q4378868_previous_loader;;
Format.pp_print_flush q4378868_formatter ();;
close_out q4378868_output;;
if not q4378868_loaded then
  failwith "Unable to load transcendental library";;

let Q4378868_PHRAGMEN_LINDELOF_THEOREM =
 `let czero = ((&0:real),(&0:real)) in
  let cone = ((&1:real),(&0:real)) in
  let cadd =
    \(z:real#real) (w:real#real).
      (FST z + FST w,SND z + SND w) in
  let cneg =
    \(z:real#real). (--(FST z),--(SND z)) in
  let csub =
    \(z:real#real) (w:real#real).
      cadd z (cneg w) in
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
      (!x:A. add x zero = x) /\
      (!x y:A. add x y = add y x) /\
      (!x y z:A. add (add x y) z = add x (add y z)) /\
      (!x:A. add x (neg x) = zero) /\
      normA zero = &0 /\
      (!x:A. smul cone x = x) /\
      (!a b:real#real. !x:A.
         smul (cmul a b) x = smul a (smul b x)) /\
      (!a b:real#real. !x:A.
         smul (cadd a b) x = add (smul a x) (smul b x)) /\
      (!a:real#real. !x y:A.
         smul a (add x y) = add (smul a x) (smul a y)) /\
      (!a:real#real. smul a zero = zero) /\
      (!x:A. smul czero x = zero) /\
      (!x:A. &0 <= normA x) /\
      (!x:A. normA x = &0 <=> x = zero) /\
      (!a:real#real. !x:A.
         normA (smul a x) = cnorm a * normA x) /\
      (!x y:A. normA (add x y) <= normA x + normA y) in
  let subA =
    \(add:A->A->A) (neg:A->A) (x:A) (y:A).
      add x (neg y) in
  let horizontal_strip =
    \(a:real) (b:real) (z:real#real).
      a < SND z /\ SND z < b in
  let in_closure_of_horizontal_strip =
    \(a:real) (b:real) (x:real#real).
      !epsilon:real.
        &0 < epsilon
        ==> ?w:real#real.
              horizontal_strip a b w /\
              cnorm (csub w x) < epsilon in
  let continuous_on_strip_closure =
    \(add:A->A->A) (neg:A->A) (normA:A->real)
     (f:(real#real)->A) (a:real) (b:real).
      !x:real#real.
        in_closure_of_horizontal_strip a b x
        ==> !epsilon:real.
              &0 < epsilon
              ==> ?delta:real.
                    &0 < delta /\
                    !y:real#real.
                      in_closure_of_horizontal_strip a b y /\
                      cnorm (csub y x) < delta
                      ==> normA (subA add neg (f y) (f x)) < epsilon in
  let complex_differentiable_within_strip_at =
    \(add:A->A->A) (neg:A->A) (smul:(real#real)->A->A)
     (normA:A->real) (f:(real#real)->A)
     (a:real) (b:real) (x:real#real).
      ?derivative:A.
        !epsilon:real.
          &0 < epsilon
          ==> ?delta:real.
                &0 < delta /\
                !y:real#real.
                  horizontal_strip a b y /\
                  cnorm (csub y x) < delta
                  ==> normA
                        (subA add neg
                          (subA add neg (f y) (f x))
                          (smul (csub y x) derivative))
                      <= epsilon * cnorm (csub y x) in
  let differentiable_on_horizontal_strip =
    \(add:A->A->A) (neg:A->A) (smul:(real#real)->A->A)
     (normA:A->real) (f:(real#real)->A)
     (a:real) (b:real).
      !x:real#real.
        horizontal_strip a b x
        ==> complex_differentiable_within_strip_at
              add neg smul normA f a b x in
  let diff_cont_on_cl =
    \(add:A->A->A) (neg:A->A) (smul:(real#real)->A->A)
     (normA:A->real) (f:(real#real)->A)
     (a:real) (b:real).
      differentiable_on_horizontal_strip
        add neg smul normA f a b /\
      continuous_on_strip_closure add neg normA f a b in
  let double_exponential_growth =
    \(normA:A->real) (f:(real#real)->A)
     (a:real) (b:real).
      ?c:real.
        c < pi / (b - a) /\
        ?B:real.
          ?Acoef:real.
            &0 < Acoef /\
            ?R:real.
              !w:real#real.
                R <= abs(FST w) /\
                horizontal_strip a b w
                ==> normA (f w)
                    <= Acoef * exp(B * exp(c * abs(FST w))) in
  !(zero:A) (add:A->A->A) (neg:A->A)
   (smul:(real#real)->A->A) (normA:A->real)
   (a:real) (b:real) (C:real)
   (f:(real#real)->A) (z:real#real).
    is_complex_normed_space zero add neg smul normA /\
    diff_cont_on_cl add neg smul normA f a b /\
    double_exponential_growth normA f a b /\
    (!w:real#real. SND w = a ==> normA (f w) <= C) /\
    (!w:real#real. SND w = b ==> normA (f w) <= C) /\
    a <= SND z /\
    SND z <= b
    ==> normA (f z) <= C`;;
