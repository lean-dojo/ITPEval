(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3229335
  (thousand-theorems__hol-light__Q3229335), "Borel–Carathéodory theorem": a
  complex-differentiable function on an open ball centered at zero whose real
  part is bounded above by a positive constant satisfies the
  Borel–Carathéodory norm estimate at every point of the ball. This file
  contains no proof.
*)

let Q3229335_BOREL_CARATHEODORY_THEOREM =
 `let czero = ((&0:real),(&0:real)) in
  let cadd =
    \(x:real#real) (y:real#real).
      (FST x + FST y,SND x + SND y) in
  let csub =
    \(x:real#real) (y:real#real).
      (FST x - FST y,SND x - SND y) in
  let cmul =
    \(x:real#real) (y:real#real).
      (FST x * FST y - SND x * SND y,
       FST x * SND y + SND x * FST y) in
  let cnorm =
    \(x:real#real).
      sqrt(FST x * FST x + SND x * SND x) in
  let open_ball_zero =
    \(R:real) (x:real#real).
      cnorm x < R in
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
  let complex_differentiable_on_open_ball =
    \(f:(real#real)->real#real) (R:real).
      !x:real#real.
        open_ball_zero R x
        ==> complex_differentiable_at f x in
  !(f:(real#real)->real#real) (M:real) (R:real) (z:real#real).
    &0 < M /\
    complex_differentiable_on_open_ball f R /\
    (!x:real#real. open_ball_zero R x ==> FST(f x) <= M) /\
    &0 < R /\
    open_ball_zero R z
    ==> cnorm(f z)
        <= &2 * M * cnorm z / (R - cnorm z) +
           cnorm(f czero) * (R + cnorm z) / (R - cnorm z)`;;
