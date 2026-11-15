(* ========================================================================= *)
(* Heron's formula for the area of a triangle.                               *)
(* ========================================================================= *)

needs "Multivariate/measure.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Eliminate square roots from formula by the usual method.                  *)
(* ------------------------------------------------------------------------- *)

let SQRT_ELIM_TAC =
  let sqrt_tm = `sqrt:real->real` in
  let is_sqrt tm = is_comb tm && rator tm = sqrt_tm in
  fun (asl,w) ->
    let stms = setify(find_terms is_sqrt w) in
    let gvs = map (genvar o type_of) stms in
    (MAP_EVERY (MP_TAC o C SPEC SQRT_POW_2 o rand) stms THEN
     EVERY (map2 (fun s v -> SPEC_TAC(s,v)) stms gvs)) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Main result.                                                              *)
(* ------------------------------------------------------------------------- *)

let HERON = `!A B C:real^2.
        let a = dist(C,B)
        and b = dist(A,C)
        and c = dist(B,A) in
        let s = (a + b + c) / &2 in
        measure(convex hull {A,B,C}) = sqrt(s * (s - a) * (s - b) * (s - c))`;;
