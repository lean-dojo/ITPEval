(* ========================================================================= *)
(* The five Platonic solids exist and there are no others.                   *)
(* ========================================================================= *)

needs "100/polyhedron.ml";;
needs "Multivariate/cross.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Some standard regular polyhedra (vertex coordinates from Wikipedia).      *)
(* ------------------------------------------------------------------------- *)

let std_tetrahedron = new_definition
 `std_tetrahedron =
     convex hull
       {vector[&1;&1;&1],vector[-- &1;-- &1;&1],
        vector[-- &1;&1;-- &1],vector[&1;-- &1;-- &1]}:real^3->bool`;;

let std_cube = new_definition
 `std_cube =
     convex hull
       {vector[&1;&1;&1],vector[&1;&1;-- &1],
        vector[&1;-- &1;&1],vector[&1;-- &1;-- &1],
        vector[-- &1;&1;&1],vector[-- &1;&1;-- &1],
        vector[-- &1;-- &1;&1],vector[-- &1;-- &1;-- &1]}:real^3->bool`;;

let std_octahedron = new_definition
 `std_octahedron =
      convex hull
       {vector[&1;&0;&0],vector[-- &1;&0;&0],
        vector[&0;&0;&1],vector[&0;&0;-- &1],
        vector[&0;&1;&0],vector[&0;-- &1;&0]}:real^3->bool`;;

let std_dodecahedron = new_definition
 `std_dodecahedron =
      let p = (&1 + sqrt(&5)) / &2 in
      convex hull
       {vector[&1;&1;&1],vector[&1;&1;-- &1],
        vector[&1;-- &1;&1],vector[&1;-- &1;-- &1],
        vector[-- &1;&1;&1],vector[-- &1;&1;-- &1],
        vector[-- &1;-- &1;&1],vector[-- &1;-- &1;-- &1],
        vector[&0;inv p;p],vector[&0;inv p;--p],
        vector[&0;--inv p;p],vector[&0;--inv p;--p],
        vector[inv p;p;&0],vector[inv p;--p;&0],
        vector[--inv p;p;&0],vector[--inv p;--p;&0],
        vector[p;&0;inv p],vector[--p;&0;inv p],
        vector[p;&0;--inv p],vector[--p;&0;--inv p]}:real^3->bool`;;

let std_icosahedron = new_definition
 `std_icosahedron =
      let p = (&1 + sqrt(&5)) / &2 in
      convex hull
       {vector[&0; &1; p],vector[&0; &1; --p],
        vector[&0; -- &1; p],vector[&0; -- &1; --p],
        vector[&1; p; &0],vector[&1; --p; &0],
        vector[-- &1; p; &0],vector[-- &1; --p; &0],
        vector[p; &0; &1],vector[--p; &0; &1],
        vector[p; &0; -- &1],vector[--p; &0; -- &1]}:real^3->bool`;;

(* ------------------------------------------------------------------------- *)
(* Slightly ad hoc conversions for computation in Q[sqrt(5)].                *)
(* Numbers are canonically represented as either a rational constant r or an *)
(* expression r1 + r2 * sqrt(5) where r2 is nonzero but r1 may be zero and   *)
(* must be present.                                                          *)
(* ------------------------------------------------------------------------- *)

let REAL_RAT5_OF_RAT_CONV =
  let pth = `p = p + &0 * sqrt(&5)`;;

let REAL_RAT5_SUB_CONV =
  let pth = `(a1 + b1 * sqrt(&5)) - (a2 + b2 * sqrt(&5)) =
      (a1 - a2) + (b1 - b2) * sqrt(&5)`;;

let REAL_RAT5_MUL_CONV =
  let pth = `(a1 + b1 * sqrt(&5)) * (a2 + b2 * sqrt(&5)) =
      (a1 * a2 + &5 * b1 * b2) + (a1 * b2 + a2 * b1) * sqrt(&5)`;;

let REAL_RAT5_INV_CONV =
  let pth = `~(a pow 2 = &5 * b pow 2)
     ==> inv(a + b * sqrt(&5)) =
         a / (a pow 2 - &5 * b pow 2) +
         --b / (a pow 2 - &5 * b pow 2) * sqrt(&5)`;;

let REAL_RAT5_EQ_CONV =
  GEN_REWRITE_CONV I [GSYM REAL_LE_ANTISYM] THENC
  BINOP_CONV REAL_RAT5_LE_CONV THENC
  GEN_REWRITE_CONV I [AND_CLAUSES];;

(* ------------------------------------------------------------------------- *)
(* Conversions for operations on 3D vectors with coordinates in Q[sqrt(5)]   *)
(* ------------------------------------------------------------------------- *)

let VECTOR3_SUB_CONV =
  let pth = `vector[x1;x2;x3] - vector[y1;y2;y3]:real^3 =
     vector[x1-y1; x2-y2; x3-y3]`;;

let VECTOR3_CROSS_CONV =
  let pth = `(vector[x1;x2;x3]) cross (vector[y1;y2;y3]) =
     vector[x2 * y3 - x3 * y2; x3 * y1 - x1 * y3; x1 * y2 - x2 * y1]`;;

let VECTOR3_EQ_0_CONV =
  let pth = `vector[x1;x2;x3]:real^3 = vec 0 <=>
        x1 = &0 /\ x2 = &0 /\ x3 = &0`;;

let STD_ICOSAHEDRON = `std_icosahedron =
   convex hull
    { vector[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)],
      vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)],
      vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)],
      vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)],
      vector[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0],
      vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0],
      vector[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0],
      vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0],
      vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1],
      vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1],
      vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1],
      vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1]}`;;

(* ------------------------------------------------------------------------- *)
(* Explicit computation of facets.                                           *)
(* ------------------------------------------------------------------------- *)

let COMPUTE_FACES_2 = `!f s:real^3->bool.
        FINITE s
        ==> (f face_of (convex hull s) /\ aff_dim f = &2 <=>
             ?x y z. x IN s /\ y IN s /\ z IN s /\
                     let a = (z - x) cross (y - x) in
                     ~(a = vec 0) /\
                     let b = a dot x in
                     ((!w. w IN s ==> a dot w <= b) \/
                      (!w. w IN s ==> a dot w >= b)) /\
                     f = convex hull (s INTER {x | a dot x = b}))`;;

let COMPUTE_FACES_2_STEP_1 = `!f v s t:real^3->bool.
       (?x y z. x IN (v INSERT s) /\ y IN (v INSERT s) /\ z IN (v INSERT s) /\
                let a = (z - x) cross (y - x) in
                ~(a = vec 0) /\
                let b = a dot x in
                ((!w. w IN t ==> a dot w <= b) \/
                 (!w. w IN t ==> a dot w >= b)) /\
                f = convex hull (t INTER {x | a dot x = b})) <=>
       (?y z. y IN s /\ z IN s /\
                let a = (z - v) cross (y - v) in
                ~(a = vec 0) /\
                let b = a dot v in
                ((!w. w IN t ==> a dot w <= b) \/
                 (!w. w IN t ==> a dot w >= b)) /\
                f = convex hull (t INTER {x | a dot x = b})) \/
       (?x y z. x IN s /\ y IN s /\ z IN s /\
                let a = (z - x) cross (y - x) in
                ~(a = vec 0) /\
                let b = a dot x in
                ((!w. w IN t ==> a dot w <= b) \/
                 (!w. w IN t ==> a dot w >= b)) /\
                f = convex hull (t INTER {x | a dot x = b}))`;;

let COMPUTE_FACES_2_STEP_2 = `!f u v s:real^3->bool.
         (?y z. y IN (u INSERT s) /\ z IN (u INSERT s) /\
                let a = (z - v) cross (y - v) in
                ~(a = vec 0) /\
                let b = a dot v in
                ((!w. w IN t ==> a dot w <= b) \/
                 (!w. w IN t ==> a dot w >= b)) /\
                f = convex hull (t INTER {x | a dot x = b})) <=>
         (?z. z IN s /\
              let a = (z - v) cross (u - v) in
              ~(a = vec 0) /\
              let b = a dot v in
              ((!w. w IN t ==> a dot w <= b) \/
               (!w. w IN t ==> a dot w >= b)) /\
              f = convex hull (t INTER {x | a dot x = b})) \/
         (?y z. y IN s /\ z IN s /\
                let a = (z - v) cross (y - v) in
                ~(a = vec 0) /\
                let b = a dot v in
                ((!w. w IN t ==> a dot w <= b) \/
                 (!w. w IN t ==> a dot w >= b)) /\
                f = convex hull (t INTER {x | a dot x = b}))`;;

let COMPUTE_FACES_TAC =
  let lemma = `(x INSERT s) INTER {x | P x} =
                        if P x then x INSERT (s INTER {x | P x})
                        else s INTER {x | P x}`;;

let CUBE_FACETS = time prove
 (`!f:real^3->bool.
        f face_of std_cube /\ aff_dim f = &2 <=>
        f = convex hull {vector[-- &1; -- &1; -- &1], vector[-- &1; -- &1; &1], vector[-- &1; &1; -- &1], vector[-- &1; &1; &1]} \/
        f = convex hull {vector[-- &1; -- &1; -- &1], vector[-- &1; -- &1; &1], vector[&1; -- &1; -- &1], vector[&1; -- &1; &1]} \/
        f = convex hull {vector[-- &1; -- &1; -- &1], vector[-- &1; &1; -- &1], vector[&1; -- &1; -- &1], vector[&1; &1; -- &1]} \/
        f = convex hull {vector[-- &1; -- &1; &1], vector[-- &1; &1; &1], vector[&1; -- &1; &1], vector[&1; &1; &1]} \/
        f = convex hull {vector[-- &1; &1; -- &1], vector[-- &1; &1; &1], vector[&1; &1; -- &1], vector[&1; &1; &1]} \/
        f = convex hull {vector[&1; -- &1; -- &1], vector[&1; -- &1; &1], vector[&1; &1; -- &1], vector[&1; &1; &1]}`,
  GEN_TAC THEN REWRITE_TAC[std_cube] THEN COMPUTE_FACES_TAC);;

let OCTAHEDRON_FACETS = time prove
 (`!f:real^3->bool.
        f face_of std_octahedron /\ aff_dim f = &2 <=>
        f = convex hull {vector[-- &1; &0; &0], vector[&0; -- &1; &0], vector[&0; &0; -- &1]} \/
        f = convex hull {vector[-- &1; &0; &0], vector[&0; -- &1; &0], vector[&0; &0; &1]} \/
        f = convex hull {vector[-- &1; &0; &0], vector[&0; &1; &0], vector[&0; &0; -- &1]} \/
        f = convex hull {vector[-- &1; &0; &0], vector[&0; &1; &0], vector[&0; &0; &1]} \/
        f = convex hull {vector[&1; &0; &0], vector[&0; -- &1; &0], vector[&0; &0; -- &1]} \/
        f = convex hull {vector[&1; &0; &0], vector[&0; -- &1; &0], vector[&0; &0; &1]} \/
        f = convex hull {vector[&1; &0; &0], vector[&0; &1; &0], vector[&0; &0; -- &1]} \/
        f = convex hull {vector[&1; &0; &0], vector[&0; &1; &0], vector[&0; &0; &1]}`,
  GEN_TAC THEN REWRITE_TAC[std_octahedron] THEN COMPUTE_FACES_TAC);;

let ICOSAHEDRON_FACETS = time prove
 (`!f:real^3->bool.
        f face_of std_icosahedron /\ aff_dim f = &2 <=>
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1], vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1], vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1], vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1], vector[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1], vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1], vector[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1], vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1], vector[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1], vector[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1], vector[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1], vector[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)]}`,
  GEN_TAC THEN REWRITE_TAC[STD_ICOSAHEDRON] THEN COMPUTE_FACES_TAC);;

let DODECAHEDRON_FACETS = time prove
 (`!f:real^3->bool.
        f face_of std_dodecahedron /\ aff_dim f = &2 <=>
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[-- &1; -- &1; -- &1], vector[-- &1; -- &1; &1]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[-- &1; &1; -- &1], vector[-- &1; &1; &1]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[-- &1; -- &1; &1], vector[-- &1; &1; &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[-- &1; -- &1; -- &1], vector[-- &1; &1; -- &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[-- &1; -- &1; -- &1], vector[&1; -- &1; -- &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[-- &1; -- &1; &1], vector[&1; -- &1; &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&1; -- &1; -- &1], vector[&1; -- &1; &1]} \/
        f = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[-- &1; &1; -- &1], vector[&1; &1; -- &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[-- &1; &1; &1], vector[&1; &1; &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&1; &1; -- &1], vector[&1; &1; &1]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[&1; -- &1; &1], vector[&1; &1; &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&1; -- &1; -- &1], vector[&1; &1; -- &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)]}`,
  GEN_TAC THEN REWRITE_TAC[STD_DODECAHEDRON] THEN COMPUTE_FACES_TAC);;

(* ------------------------------------------------------------------------- *)
(* Given a coplanar set, return a hyperplane containing it.                  *)
(* Maps term s to theorem |- !x. x IN s ==> n dot x = d                      *)
(* Currently assumes |s| >= 3 but it would be trivial to do other cases.     *)
(* ------------------------------------------------------------------------- *)

let COPLANAR_HYPERPLANE_RULE =
  let rec allsets m l =
    if m = 0 then [[]] else
    match l with
      [] -> []
    | h::t -> map (fun g -> h::g) (allsets (m - 1) t) @ allsets m t in
  let mk_sub = mk_binop `(-):real^3->real^3->real^3`
  and mk_cross = mk_binop `cross`
  and mk_dot = mk_binop `(dot):real^3->real^3->real`
  and zerovec_tm = `vector[&0;&0;&0]:real^3`
  and template = `(!x:real^3. x IN s ==> n dot x = d)`
  and s_tm = `s:real^3->bool`
  and n_tm = `n:real^3`
  and d_tm = `d:real` in
  let mk_normal [x;y;z] = mk_cross (mk_sub y x) (mk_sub z x) in
  let eval_normal t =
    (BINOP_CONV VECTOR3_SUB_CONV THENC VECTOR3_CROSS_CONV) (mk_normal t) in
  let check_normal t =
    let th = eval_normal t in
    let n = rand(concl th) in
    if n = zerovec_tm then failwith "check_normal" else n in
  fun tm ->
    let s = dest_setenum tm in
    if length s < 3 then failwith "COPLANAR_HYPERPLANE_RULE: trivial" else
    let n = tryfind check_normal (allsets 3 s) in
    let d = rand(concl(VECTOR3_DOT_CONV(mk_dot n (hd s)))) in
    let ptm = vsubst [tm,s_tm; n,n_tm; d,d_tm] template in
    EQT_ELIM
    ((REWRITE_CONV[FORALL_IN_INSERT; NOT_IN_EMPTY] THENC
      DEPTH_BINOP_CONV `/\`
       (LAND_CONV VECTOR3_DOT_CONV THENC REAL_RAT5_EQ_CONV) THENC
      GEN_REWRITE_CONV DEPTH_CONV [AND_CLAUSES]) ptm);;

(* ------------------------------------------------------------------------- *)
(* Explicit computation of edges, assuming hyperplane containing the set.    *)
(* ------------------------------------------------------------------------- *)

let COMPUTE_FACES_1 = `!s:real^3->bool n d.
        (!x. x IN s ==> n dot x = d)
        ==> FINITE s /\ ~(n = vec 0)
            ==> !f. f face_of (convex hull s) /\ aff_dim f = &1 <=>
                    ?x y. x IN s /\ y IN s /\
                          let a = n cross (y - x) in
                          ~(a = vec 0) /\
                          let b = a dot x in
                          ((!w. w IN s ==> a dot w <= b) \/
                           (!w. w IN s ==> a dot w >= b)) /\
                          f = convex hull (s INTER {x | a dot x = b})`;;

(* ------------------------------------------------------------------------- *)
(* Given a coplanar set, return exhaustive edge case theorem.                *)
(* ------------------------------------------------------------------------- *)

let COMPUTE_EDGES_CONV =
  let lemma = `(x INSERT s) INTER {x | P x} =
                        if P x then x INSERT (s INTER {x | P x})
                        else s INTER {x | P x}`;;

let EDGES_PER_FACE_TAC th =
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `CARD  {e:real^3->bool | e face_of f /\ aff_dim(e) = &1}` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[FACE_OF_FACE; FACE_OF_TRANS; FACE_OF_IMP_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPEC `f:real^3->bool` th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  W(fun (_,w) -> REWRITE_TAC[COMPUTE_EDGES_CONV(find_term is_setenum w)]) THEN
  REWRITE_TAC[SET_RULE `x = a \/ x = b <=> x IN {a,b}`] THEN
  REWRITE_TAC[GSYM IN_INSERT; SET_RULE `{x | x IN s} = s`] THEN
  REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC
   (MESON[HAS_SIZE] `s HAS_SIZE n ==> CARD s = n`) THEN
  REPEAT
  (MATCH_MP_TAC CARD_EQ_LEMMA THEN REPEAT CONJ_TAC THENL
    [CONV_TAC NUM_REDUCE_CONV THEN NO_TAC;
     REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; SEGMENT_EQ; DE_MORGAN_THM] THEN
     REPEAT CONJ_TAC THEN MATCH_MP_TAC(SET_RULE
      `~(a = c /\ b = d) /\ ~(a = d /\ b = c) /\ ~(a = b /\ c = d)
       ==> ~({a,b} = {c,d})`) THEN
     PURE_ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
     CONV_TAC(ONCE_DEPTH_CONV VECTOR3_SUB_CONV) THEN
     CONV_TAC(ONCE_DEPTH_CONV VECTOR3_EQ_0_CONV) THEN
     REWRITE_TAC[] THEN NO_TAC;
     ALL_TAC]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[CONJUNCT1 HAS_SIZE_CLAUSES];;

let TETRAHEDRON_EDGES_PER_FACE = `!f. f face_of std_tetrahedron /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_tetrahedron /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 3`;;

let CUBE_EDGES_PER_FACE = `!f. f face_of std_cube /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_cube /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 4`;;

let OCTAHEDRON_EDGES_PER_FACE = `!f. f face_of std_octahedron /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_octahedron /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 3`;;

let DODECAHEDRON_EDGES_PER_FACE = `!f. f face_of std_dodecahedron /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_dodecahedron /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 5`;;

let ICOSAHEDRON_EDGES_PER_FACE = `!f. f face_of std_icosahedron /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_icosahedron /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 3`;;

(* ------------------------------------------------------------------------- *)
(* Show that the Platonic solids are all full-dimensional.                   *)
(* ------------------------------------------------------------------------- *)

let POLYTOPE_3D_LEMMA = `(let a = (z - x) cross (y - x) in
    ~(a = vec 0) /\ ?w. w IN s /\ ~(a dot w = a dot x))
   ==> aff_dim(convex hull (x INSERT y INSERT z INSERT s:real^3->bool)) = &3`;;

let POLYTOPE_FULLDIM_TAC =
  MATCH_MP_TAC POLYTOPE_3D_LEMMA THEN
  CONV_TAC(ONCE_DEPTH_CONV VECTOR3_SUB_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV VECTOR3_CROSS_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN CONJ_TAC THENL
   [CONV_TAC(RAND_CONV VECTOR3_EQ_0_CONV) THEN REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV VECTOR3_DOT_CONV) THEN
    REWRITE_TAC[EXISTS_IN_INSERT; NOT_IN_EMPTY] THEN
    CONV_TAC(ONCE_DEPTH_CONV VECTOR3_DOT_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT5_EQ_CONV) THEN
    REWRITE_TAC[]];;

let STD_TETRAHEDRON_FULLDIM = `aff_dim std_tetrahedron = &3`;;

let STD_CUBE_FULLDIM = `aff_dim std_cube = &3`;;

let STD_OCTAHEDRON_FULLDIM = `aff_dim std_octahedron = &3`;;

let STD_DODECAHEDRON_FULLDIM = `aff_dim std_dodecahedron = &3`;;

let STD_ICOSAHEDRON_FULLDIM = `aff_dim std_icosahedron = &3`;;

(* ------------------------------------------------------------------------- *)
(* Complete list of edges for each Platonic solid.                           *)
(* ------------------------------------------------------------------------- *)

let COMPUTE_EDGES_TAC defn fulldim facets =
  GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   (vsubst[lhs(concl defn),`p:real^3->bool`]
      `?f:real^3->bool. (f face_of p /\ aff_dim f = &2) /\
                        (e face_of f /\ aff_dim e = &1)`) THEN
  CONJ_TAC THENL
   [EQ_TAC THENL [STRIP_TAC; MESON_TAC[FACE_OF_TRANS]] THEN
    MP_TAC(ISPECL [lhs(concl defn); `e:real^3->bool`]
        FACE_OF_POLYHEDRON_SUBSET_FACET) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[defn] THEN
        MATCH_MP_TAC POLYHEDRON_CONVEX_HULL THEN
        REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
        CONJ_TAC THEN
        DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^3->bool)->int`) THEN
        ASM_REWRITE_TAC[fulldim; AFF_DIM_EMPTY] THEN
        CONV_TAC INT_REDUCE_CONV];
      MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[facet_of] THEN
      REWRITE_TAC[fulldim] THEN CONV_TAC INT_REDUCE_CONV THEN
      ASM_MESON_TAC[FACE_OF_FACE]];
    REWRITE_TAC[facets] THEN
    REWRITE_TAC[TAUT `(a \/ b) /\ c <=> a /\ c \/ b /\ c`] THEN
    REWRITE_TAC[EXISTS_OR_THM; UNWIND_THM2] THEN
    CONV_TAC(LAND_CONV(DEPTH_BINOP_CONV `\/`
     (fun tm -> REWR_CONV (COMPUTE_EDGES_CONV(rand(rand(lhand tm)))) tm))) THEN
    REWRITE_TAC[INSERT_AC] THEN REWRITE_TAC[DISJ_ACI]];;

let TETRAHEDRON_EDGES = `!e. e face_of std_tetrahedron /\ aff_dim e = &1 <=>
       e = convex hull {vector[-- &1; -- &1; &1], vector[-- &1; &1; -- &1]} \/
       e = convex hull {vector[-- &1; -- &1; &1], vector[&1; -- &1; -- &1]} \/
       e = convex hull {vector[-- &1; -- &1; &1], vector[&1; &1; &1]} \/
       e = convex hull {vector[-- &1; &1; -- &1], vector[&1; -- &1; -- &1]} \/
       e = convex hull {vector[-- &1; &1; -- &1], vector[&1; &1; &1]} \/
       e = convex hull {vector[&1; -- &1; -- &1], vector[&1; &1; &1]}`;;

let CUBE_EDGES = `!e. e face_of std_cube /\ aff_dim e = &1 <=>
       e = convex hull {vector[-- &1; -- &1; -- &1], vector[-- &1; -- &1; &1]} \/
       e = convex hull {vector[-- &1; -- &1; -- &1], vector[-- &1; &1; -- &1]} \/
       e = convex hull {vector[-- &1; -- &1; -- &1], vector[&1; -- &1; -- &1]} \/
       e = convex hull {vector[-- &1; -- &1; &1], vector[-- &1; &1; &1]} \/
       e = convex hull {vector[-- &1; -- &1; &1], vector[&1; -- &1; &1]} \/
       e = convex hull {vector[-- &1; &1; -- &1], vector[-- &1; &1; &1]} \/
       e = convex hull {vector[-- &1; &1; -- &1], vector[&1; &1; -- &1]} \/
       e = convex hull {vector[-- &1; &1; &1], vector[&1; &1; &1]} \/
       e = convex hull {vector[&1; -- &1; -- &1], vector[&1; -- &1; &1]} \/
       e = convex hull {vector[&1; -- &1; -- &1], vector[&1; &1; -- &1]} \/
       e = convex hull {vector[&1; -- &1; &1], vector[&1; &1; &1]} \/
       e = convex hull {vector[&1; &1; -- &1], vector[&1; &1; &1]}`;;

let OCTAHEDRON_EDGES = `!e. e face_of std_octahedron /\ aff_dim e = &1 <=>
       e = convex hull {vector[-- &1; &0; &0], vector[&0; -- &1; &0]} \/
       e = convex hull {vector[-- &1; &0; &0], vector[&0; &1; &0]} \/
       e = convex hull {vector[-- &1; &0; &0], vector[&0; &0; -- &1]} \/
       e = convex hull {vector[-- &1; &0; &0], vector[&0; &0; &1]} \/
       e = convex hull {vector[&1; &0; &0], vector[&0; -- &1; &0]} \/
       e = convex hull {vector[&1; &0; &0], vector[&0; &1; &0]} \/
       e = convex hull {vector[&1; &0; &0], vector[&0; &0; -- &1]} \/
       e = convex hull {vector[&1; &0; &0], vector[&0; &0; &1]} \/
       e = convex hull {vector[&0; -- &1; &0], vector[&0; &0; -- &1]} \/
       e = convex hull {vector[&0; -- &1; &0], vector[&0; &0; &1]} \/
       e = convex hull {vector[&0; &1; &0], vector[&0; &0; -- &1]} \/
       e = convex hull {vector[&0; &1; &0], vector[&0; &0; &1]}`;;

let DODECAHEDRON_EDGES = `!e. e face_of std_dodecahedron /\ aff_dim e = &1 <=>
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[-- &1; -- &1; &1]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[-- &1; &1; &1]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[-- &1; -- &1; -- &1]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[-- &1; &1; -- &1]} \/
       e = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&1; -- &1; -- &1]} \/
       e = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&1; -- &1; &1]} \/
       e = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&1; &1; -- &1]} \/
       e = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&1; &1; &1]} \/
       e = convex hull {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[-- &1; -- &1; -- &1]} \/
       e = convex hull {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[-- &1; -- &1; &1]} \/
       e = convex hull {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[-- &1; &1; -- &1]} \/
       e = convex hull {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[-- &1; &1; &1]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[&1; -- &1; &1]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[&1; &1; &1]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[&1; -- &1; -- &1]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[&1; &1; -- &1]} \/
       e = convex hull {vector[-- &1; -- &1; -- &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; -- &1; &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; &1; -- &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; &1; &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; -- &1; -- &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; -- &1; &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; &1; -- &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; &1; &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]}`;;

let ICOSAHEDRON_EDGES = `!e. e face_of std_icosahedron /\ aff_dim e = &1 <=>
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1], vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1], vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1], vector[-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1], vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1], vector[-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1], vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1], vector[&1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1], vector[&1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]}`;;

(* ------------------------------------------------------------------------- *)
(* Enumerate all the vertices.                                               *)
(* ------------------------------------------------------------------------- *)

let COMPUTE_VERTICES_TAC defn fulldim edges =
  GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   (vsubst[lhs(concl defn),`p:real^3->bool`]
      `?e:real^3->bool. (e face_of p /\ aff_dim e = &1) /\
                        (v face_of e /\ aff_dim v = &0)`) THEN
  CONJ_TAC THENL
   [EQ_TAC THENL [STRIP_TAC; MESON_TAC[FACE_OF_TRANS]] THEN
    MP_TAC(ISPECL [lhs(concl defn); `v:real^3->bool`]
        FACE_OF_POLYHEDRON_SUBSET_FACET) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[defn] THEN
        MATCH_MP_TAC POLYHEDRON_CONVEX_HULL THEN
        REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
        CONJ_TAC THEN
        DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^3->bool)->int`) THEN
        ASM_REWRITE_TAC[fulldim; AFF_DIM_EMPTY] THEN
        CONV_TAC INT_REDUCE_CONV];
      REWRITE_TAC[facet_of] THEN
      DISCH_THEN(X_CHOOSE_THEN `f:real^3->bool` STRIP_ASSUME_TAC)] THEN
    MP_TAC(ISPECL [`f:real^3->bool`; `v:real^3->bool`]
        FACE_OF_POLYHEDRON_SUBSET_FACET) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC FACE_OF_POLYHEDRON_POLYHEDRON THEN
        FIRST_ASSUM(fun th ->
          EXISTS_TAC (rand(concl th)) THEN
          CONJ_TAC THENL [ALL_TAC; ACCEPT_TAC th]) THEN
        REWRITE_TAC[defn] THEN
        MATCH_MP_TAC POLYHEDRON_CONVEX_HULL THEN
        REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
        ASM_MESON_TAC[FACE_OF_FACE];
        DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^3->bool)->int`) THEN
        ASM_REWRITE_TAC[fulldim; AFF_DIM_EMPTY] THEN
        CONV_TAC INT_REDUCE_CONV;
        DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^3->bool)->int`) THEN
        ASM_REWRITE_TAC[fulldim; AFF_DIM_EMPTY] THEN
        CONV_TAC INT_REDUCE_CONV];
      MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[facet_of] THEN
      ASM_REWRITE_TAC[fulldim] THEN CONV_TAC INT_REDUCE_CONV THEN
      ASM_MESON_TAC[FACE_OF_FACE; FACE_OF_TRANS]];
    REWRITE_TAC[edges] THEN
    REWRITE_TAC[TAUT `(a \/ b) /\ c <=> a /\ c \/ b /\ c`] THEN
    REWRITE_TAC[EXISTS_OR_THM; UNWIND_THM2] THEN
    REWRITE_TAC[AFF_DIM_EQ_0; RIGHT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[MESON[]
     `v face_of s /\ v = {a} <=> {a} face_of s /\ v = {a}`] THEN
    REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; FACE_OF_SING] THEN
    REWRITE_TAC[EXTREME_POINT_OF_SEGMENT] THEN
    REWRITE_TAC[TAUT `(a \/ b) /\ c <=> a /\ c \/ b /\ c`] THEN
    REWRITE_TAC[EXISTS_OR_THM; UNWIND_THM2] THEN
    REWRITE_TAC[DISJ_ACI]];;

let TETRAHEDRON_VERTICES = `!v. v face_of std_tetrahedron /\ aff_dim v = &0 <=>
       v = {vector [-- &1; -- &1; &1]} \/
       v = {vector [-- &1; &1; -- &1]} \/
       v = {vector [&1; -- &1; -- &1]} \/
       v = {vector [&1; &1; &1]}`;;

let CUBE_VERTICES = `!v. v face_of std_cube /\ aff_dim v = &0 <=>
       v = {vector [-- &1; -- &1; -- &1]} \/
       v = {vector [-- &1; -- &1; &1]} \/
       v = {vector [-- &1; &1; -- &1]} \/
       v = {vector [-- &1; &1; &1]} \/
       v = {vector [&1; -- &1; -- &1]} \/
       v = {vector [&1; -- &1; &1]} \/
       v = {vector [&1; &1; -- &1]} \/
       v = {vector [&1; &1; &1]}`;;

let OCTAHEDRON_VERTICES = `!v. v face_of std_octahedron /\ aff_dim v = &0 <=>
       v = {vector [-- &1; &0; &0]} \/
       v = {vector [&1; &0; &0]} \/
       v = {vector [&0; -- &1; &0]} \/
       v = {vector [&0; &1; &0]} \/
       v = {vector [&0; &0; -- &1]} \/
       v = {vector [&0; &0; &1]}`;;

let DODECAHEDRON_VERTICES = `!v. v face_of std_dodecahedron /\ aff_dim v = &0 <=>
       v = {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       v = {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       v = {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       v = {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       v = {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       v = {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       v = {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       v = {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       v = {vector[-- &1; -- &1; -- &1]} \/
       v = {vector[-- &1; -- &1; &1]} \/
       v = {vector[-- &1; &1; -- &1]} \/
       v = {vector[-- &1; &1; &1]} \/
       v = {vector[&1; -- &1; -- &1]} \/
       v = {vector[&1; -- &1; &1]} \/
       v = {vector[&1; &1; -- &1]} \/
       v = {vector[&1; &1; &1]} \/
       v = {vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       v = {vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       v = {vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       v = {vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]}`;;

let ICOSAHEDRON_VERTICES = `!v. v face_of std_icosahedron /\ aff_dim v = &0 <=>
       v = {vector [-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1]} \/
       v = {vector [-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1]} \/
       v = {vector [&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1]} \/
       v = {vector [&1 / &2 + &1 / &2 * sqrt (&5); &0; &1]} \/
       v = {vector [-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       v = {vector [-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       v = {vector [&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       v = {vector [&1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       v = {vector [&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       v = {vector [&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       v = {vector [&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       v = {vector [&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]}`;;

(* ------------------------------------------------------------------------- *)
(* Number of edges meeting at each vertex.                                   *)
(* ------------------------------------------------------------------------- *)

let EDGES_PER_VERTEX_TAC defn edges verts =
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   (vsubst[lhs(concl defn),`p:real^3->bool`]
     `CARD {e | (e face_of p /\ aff_dim(e) = &1) /\
                (v:real^3->bool) face_of e}`) THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    ASM_MESON_TAC[FACE_OF_FACE];
    ALL_TAC] THEN
  MP_TAC(ISPEC `v:real^3->bool` verts) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[edges] THEN
  REWRITE_TAC[SET_RULE
   `{e | (P e \/ Q e) /\ R e} =
    {e | P e /\ R e} UNION {e | Q e /\ R e}`] THEN
  REWRITE_TAC[MESON[FACE_OF_SING]
   `e = a /\ {x} face_of e <=> e = a /\ x extreme_point_of a`] THEN
  REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; EXTREME_POINT_OF_SEGMENT] THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV VECTOR3_SUB_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV VECTOR3_EQ_0_CONV) THEN
  REWRITE_TAC[EMPTY_GSPEC; UNION_EMPTY] THEN
  REWRITE_TAC[SET_RULE `{x | x = a} = {a}`] THEN
  REWRITE_TAC[SET_RULE `{x} UNION s = x INSERT s`] THEN MATCH_MP_TAC
   (MESON[HAS_SIZE] `s HAS_SIZE n ==> CARD s = n`) THEN
  REPEAT
  (MATCH_MP_TAC CARD_EQ_LEMMA THEN REPEAT CONJ_TAC THENL
    [CONV_TAC NUM_REDUCE_CONV THEN NO_TAC;
     REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM; SEGMENT_EQ] THEN
     REPEAT CONJ_TAC THEN MATCH_MP_TAC(SET_RULE
      `~(a = c /\ b = d) /\ ~(a = d /\ b = c) /\ ~(a = b /\ c = d)
       ==> ~({a,b} = {c,d})`) THEN
     PURE_ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
     CONV_TAC(ONCE_DEPTH_CONV VECTOR3_SUB_CONV) THEN
     CONV_TAC(ONCE_DEPTH_CONV VECTOR3_EQ_0_CONV) THEN
     REWRITE_TAC[] THEN NO_TAC;
     ALL_TAC]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[CONJUNCT1 HAS_SIZE_CLAUSES];;

let TETRAHEDRON_EDGES_PER_VERTEX = `!v. v face_of std_tetrahedron /\ aff_dim(v) = &0
       ==> CARD {e | e face_of std_tetrahedron /\ aff_dim(e) = &1 /\
                     v SUBSET e} = 3`;;

let CUBE_EDGES_PER_VERTEX = `!v. v face_of std_cube /\ aff_dim(v) = &0
       ==> CARD {e | e face_of std_cube /\ aff_dim(e) = &1 /\
                     v SUBSET e} = 3`;;

let OCTAHEDRON_EDGES_PER_VERTEX = `!v. v face_of std_octahedron /\ aff_dim(v) = &0
       ==> CARD {e | e face_of std_octahedron /\ aff_dim(e) = &1 /\
                     v SUBSET e} = 4`;;

let DODECAHEDRON_EDGES_PER_VERTEX = `!v. v face_of std_dodecahedron /\ aff_dim(v) = &0
       ==> CARD {e | e face_of std_dodecahedron /\ aff_dim(e) = &1 /\
                     v SUBSET e} = 3`;;

let ICOSAHEDRON_EDGES_PER_VERTEX = `!v. v face_of std_icosahedron /\ aff_dim(v) = &0
       ==> CARD {e | e face_of std_icosahedron /\ aff_dim(e) = &1 /\
                     v SUBSET e} = 5`;;

(* ------------------------------------------------------------------------- *)
(* Number of Platonic solids.                                                *)
(* ------------------------------------------------------------------------- *)

let MULTIPLE_COUNTING_LEMMA = `!R:A->B->bool s t.
        FINITE s /\ FINITE t /\
        (!x. x IN s ==> CARD {y | y IN t /\ R x y} = m) /\
        (!y. y IN t ==> CARD {x | x IN s /\ R x y} = n)
        ==> m * CARD s = n * CARD t`;;

let SIZE_ZERO_DIMENSIONAL_FACES = `!s:real^N->bool.
        polyhedron s
        ==> CARD {f | f face_of s /\ aff_dim f = &0} =
            CARD {v | v extreme_point_of s} /\
            (FINITE {f | f face_of s /\ aff_dim f = &0} <=>
             FINITE {v | v extreme_point_of s}) /\
            (!n. {f | f face_of s /\ aff_dim f = &0} HAS_SIZE n <=>
                 {v | v extreme_point_of s} HAS_SIZE n)`;;

let PLATONIC_SOLIDS_LIMITS = `!p:real^3->bool m n.
    polytope p /\ aff_dim p = &3 /\
    (!f. f face_of p /\ aff_dim(f) = &2
         ==> CARD {e | e face_of p /\ aff_dim(e) = &1 /\ e SUBSET f} = m) /\
    (!v. v face_of p /\ aff_dim(v) = &0
         ==> CARD {e | e face_of p /\ aff_dim(e) = &1 /\ v SUBSET e} = n)
    ==> m = 3 /\ n = 3 \/       // Tetrahedron
        m = 4 /\ n = 3 \/       // Cube
        m = 3 /\ n = 4 \/       // Octahedron
        m = 5 /\ n = 3 \/       // Dodecahedron
        m = 3 /\ n = 5          // Icosahedron`;;

(* ------------------------------------------------------------------------- *)
(* If-and-only-if version.                                                   *)
(* ------------------------------------------------------------------------- *)

let PLATONIC_SOLIDS = `!m n.
   (?p:real^3->bool.
     polytope p /\ aff_dim p = &3 /\
     (!f. f face_of p /\ aff_dim(f) = &2
          ==> CARD {e | e face_of p /\ aff_dim(e) = &1 /\ e SUBSET f} = m) /\
     (!v. v face_of p /\ aff_dim(v) = &0
          ==> CARD {e | e face_of p /\ aff_dim(e) = &1 /\ v SUBSET e} = n)) <=>
     m = 3 /\ n = 3 \/       // Tetrahedron
     m = 4 /\ n = 3 \/       // Cube
     m = 3 /\ n = 4 \/       // Octahedron
     m = 5 /\ n = 3 \/       // Dodecahedron
     m = 3 /\ n = 5          // Icosahedron`;;

(* ------------------------------------------------------------------------- *)
(* Show that the regular polyhedra do have all edges and faces congruent.    *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("congruent",(12,"right"));;

let congruent = new_definition
 `(s:real^N->bool) congruent (t:real^N->bool) <=>
        ?c f. orthogonal_transformation f /\ t = IMAGE (\x. c + f x) s`;;

let CONGRUENT_SIMPLE = `(?A:real^3^3. orthogonal_matrix A /\ IMAGE (\x:real^3. A ** x) s = t)
   ==> (convex hull s) congruent (convex hull t)`;;

let CONGRUENT_SEGMENTS = `!a b c d:real^N.
        dist(a,b) = dist(c,d)
        ==> segment[a,b] congruent segment[c,d]`;;

let compute_dist =
  let mk_sub = mk_binop `(-):real^3->real^3->real^3`
  and dot_tm = `(dot):real^3->real^3->real` in
  fun v1 v2 -> let vth = VECTOR3_SUB_CONV(mk_sub v1 v2) in
               let dth = CONV_RULE(RAND_CONV VECTOR3_DOT_CONV)
                          (MK_COMB(AP_TERM dot_tm vth,vth)) in
               rand(concl dth);;

let le_rat5 =
  let mk_le = mk_binop `(<=):real->real->bool` and t_tm = `T` in
  fun r1 r2 -> rand(concl(REAL_RAT5_LE_CONV(mk_le r1 r2))) = t_tm;;

let three_adjacent_points s =
  match s with
  | x::t -> let (y,_)::(z,_)::_ =
              sort (fun (_,r1) (_,r2) -> le_rat5 r1 r2)
                   (map (fun y -> y,compute_dist x y) t) in
            x,y,z
  | _ -> failwith "three_adjacent_points: no points";;

let mk_33matrix =
  let a11_tm = `a11:real`
  and a12_tm = `a12:real`
  and a13_tm = `a13:real`
  and a21_tm = `a21:real`
  and a22_tm = `a22:real`
  and a23_tm = `a23:real`
  and a31_tm = `a31:real`
  and a32_tm = `a32:real`
  and a33_tm = `a33:real`
  and pat_tm =
   `vector[vector[a11; a12; a13];
           vector[a21; a22; a23];
           vector[a31; a32; a33]]:real^3^3` in
  fun [a11;a12;a13;a21;a22;a23;a31;a32;a33] ->
    vsubst[a11,a11_tm;
           a12,a12_tm;
           a13,a13_tm;
           a21,a21_tm;
           a22,a22_tm;
           a23,a23_tm;
           a31,a31_tm;
           a32,a32_tm;
           a33,a33_tm] pat_tm;;

let MATRIX_VECTOR_MUL_3 = `(vector[vector[a11;a12;a13];
           vector[a21; a22; a23];
           vector[a31; a32; a33]]:real^3^3) **
   (vector[x1;x2;x3]:real^3) =
   vector[a11 * x1 + a12 * x2 + a13 * x3;
          a21 * x1 + a22 * x2 + a23 * x3;
          a31 * x1 + a32 * x2 + a33 * x3]`;;

let MATRIX_LEMMA = `!A:real^3^3.
   A ** x1 = x2 /\
   A ** y1 = y2 /\
   A ** z1 = z2 <=>
   (vector [x1; y1; z1]:real^3^3) ** (row 1 A:real^3) =
   vector [x2$1; y2$1; z2$1] /\
   (vector [x1; y1; z1]:real^3^3) ** (row 2 A:real^3) =
   vector [x2$2; y2$2; z2$2] /\
   (vector [x1; y1; z1]:real^3^3) ** (row 3 A:real^3) =
   vector [x2$3; y2$3; z2$3]`;;

let MATRIX_BY_CRAMER_LEMMA = `!A:real^3^3.
        ~(det(vector[x1; y1; z1]:real^3^3) = &0)
        ==> (A ** x1 = x2 /\
             A ** y1 = y2 /\
             A ** z1 = z2 <=>
             A = lambda m k. det((lambda i j.
                                  if j = k
                                  then (vector[x2$m; y2$m; z2$m]:real^3)$i
                                  else (vector[x1; y1; z1]:real^3^3)$i$j)
                                 :real^3^3) /
                             det(vector[x1;y1;z1]:real^3^3))`;;

let MATRIX_BY_CRAMER = `!A:real^3^3 x1 y1 z1 x2 y2 z2.
        let d = det(vector[x1; y1; z1]:real^3^3) in
        ~(d = &0)
        ==> (A ** x1 = x2 /\
             A ** y1 = y2 /\
             A ** z1 = z2 <=>
               A$1$1 =
               (x2$1 * y1$2 * z1$3 +
                x1$2 * y1$3 * z2$1 +
                x1$3 * y2$1 * z1$2 -
                x2$1 * y1$3 * z1$2 -
                x1$2 * y2$1 * z1$3 -
                x1$3 * y1$2 * z2$1) / d /\
               A$1$2 =
               (x1$1 * y2$1 * z1$3 +
                x2$1 * y1$3 * z1$1 +
                x1$3 * y1$1 * z2$1 -
                x1$1 * y1$3 * z2$1 -
                x2$1 * y1$1 * z1$3 -
                x1$3 * y2$1 * z1$1) / d /\
               A$1$3 =
               (x1$1 * y1$2 * z2$1 +
                x1$2 * y2$1 * z1$1 +
                x2$1 * y1$1 * z1$2 -
                x1$1 * y2$1 * z1$2 -
                x1$2 * y1$1 * z2$1 -
                x2$1 * y1$2 * z1$1) / d /\
               A$2$1 =
               (x2$2 * y1$2 * z1$3 +
                x1$2 * y1$3 * z2$2 +
                x1$3 * y2$2 * z1$2 -
                x2$2 * y1$3 * z1$2 -
                x1$2 * y2$2 * z1$3 -
                x1$3 * y1$2 * z2$2) / d /\
               A$2$2 =
               (x1$1 * y2$2 * z1$3 +
                x2$2 * y1$3 * z1$1 +
                x1$3 * y1$1 * z2$2 -
                x1$1 * y1$3 * z2$2 -
                x2$2 * y1$1 * z1$3 -
                x1$3 * y2$2 * z1$1) / d /\
               A$2$3 =
               (x1$1 * y1$2 * z2$2 +
                x1$2 * y2$2 * z1$1 +
                x2$2 * y1$1 * z1$2 -
                x1$1 * y2$2 * z1$2 -
                x1$2 * y1$1 * z2$2 -
                x2$2 * y1$2 * z1$1) / d /\
               A$3$1 =
               (x2$3 * y1$2 * z1$3 +
                x1$2 * y1$3 * z2$3 +
                x1$3 * y2$3 * z1$2 -
                x2$3 * y1$3 * z1$2 -
                x1$2 * y2$3 * z1$3 -
                x1$3 * y1$2 * z2$3) / d /\
               A$3$2 =
               (x1$1 * y2$3 * z1$3 +
                x2$3 * y1$3 * z1$1 +
                x1$3 * y1$1 * z2$3 -
                x1$1 * y1$3 * z2$3 -
                x2$3 * y1$1 * z1$3 -
                x1$3 * y2$3 * z1$1) / d /\
               A$3$3 =
               (x1$1 * y1$2 * z2$3 +
                x1$2 * y2$3 * z1$1 +
                x2$3 * y1$1 * z1$2 -
                x1$1 * y2$3 * z1$2 -
                x1$2 * y1$1 * z2$3 -
                x2$3 * y1$2 * z1$1) / d)`;;

let CONGRUENT_EDGES_TAC edges =
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REWRITE_TAC[IMP_IMP] THEN
  REWRITE_TAC[edges] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN
  MATCH_MP_TAC CONGRUENT_SEGMENTS THEN REWRITE_TAC[DIST_EQ] THEN
  REWRITE_TAC[dist; NORM_POW_2] THEN
  CONV_TAC(ONCE_DEPTH_CONV VECTOR3_SUB_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV VECTOR3_DOT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT5_EQ_CONV) THEN
  REWRITE_TAC[];;

let CONGRUENT_FACES_TAC facets =
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REWRITE_TAC[IMP_IMP] THEN
  REWRITE_TAC[facets] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  W(fun (asl,w) ->
        let t1 = rand(lhand w) and t2 = rand(rand w) in
        let (x1,y1,z1) = three_adjacent_points (dest_setenum t1)
        and (x2,y2,z2) = three_adjacent_points (dest_setenum t2) in
        let th1 = SPECL [`A:real^3^3`;x1;y1;z1;x2;y2;z2] MATRIX_BY_CRAMER in
        let th2 = REWRITE_RULE[VECTOR_3; DET_3] th1 in
        let th3 = CONV_RULE (DEPTH_CONV REAL_RAT5_MUL_CONV) th2 in
        let th4 = CONV_RULE (DEPTH_CONV
         (REAL_RAT5_ADD_CONV ORELSEC REAL_RAT5_SUB_CONV)) th3 in
        let th5 = CONV_RULE let_CONV th4 in
        let th6 = CONV_RULE(ONCE_DEPTH_CONV REAL_RAT5_DIV_CONV) th5 in
        let th7 = CONV_RULE(ONCE_DEPTH_CONV REAL_RAT5_EQ_CONV) th6 in
        let th8 = MP th7 (EQT_ELIM(REWRITE_CONV[] (lhand(concl th7)))) in
        let tms = map rhs (conjuncts(rand(concl th8))) in
        let matt = mk_33matrix tms in
        MATCH_MP_TAC CONGRUENT_SIMPLE THEN EXISTS_TAC matt THEN CONJ_TAC THENL
         [REWRITE_TAC[ORTHOGONAL_MATRIX; CART_EQ] THEN
          SIMP_TAC[transp; LAMBDA_BETA; matrix_mul; mat] THEN
          REWRITE_TAC[DIMINDEX_3; SUM_3; FORALL_3; VECTOR_3; ARITH] THEN
          CONV_TAC(ONCE_DEPTH_CONV REAL_RAT5_MUL_CONV) THEN
          CONV_TAC(DEPTH_CONV REAL_RAT5_ADD_CONV) THEN
          CONV_TAC(ONCE_DEPTH_CONV REAL_RAT5_EQ_CONV) THEN
          REWRITE_TAC[] THEN NO_TAC;
          REWRITE_TAC[IMAGE_CLAUSES; MATRIX_VECTOR_MUL_3] THEN
          CONV_TAC(ONCE_DEPTH_CONV REAL_RAT5_MUL_CONV) THEN
          CONV_TAC(DEPTH_CONV REAL_RAT5_ADD_CONV) THEN
          REWRITE_TAC[INSERT_AC]]);;

let TETRAHEDRON_CONGRUENT_EDGES = `!e1 e2. e1 face_of std_tetrahedron /\ aff_dim e1 = &1 /\
           e2 face_of std_tetrahedron /\ aff_dim e2 = &1
           ==> e1 congruent e2`;;

let TETRAHEDRON_CONGRUENT_FACETS = `!f1 f2. f1 face_of std_tetrahedron /\ aff_dim f1 = &2 /\
           f2 face_of std_tetrahedron /\ aff_dim f2 = &2
           ==> f1 congruent f2`;;

let CUBE_CONGRUENT_EDGES = `!e1 e2. e1 face_of std_cube /\ aff_dim e1 = &1 /\
           e2 face_of std_cube /\ aff_dim e2 = &1
           ==> e1 congruent e2`;;

let CUBE_CONGRUENT_FACETS = `!f1 f2. f1 face_of std_cube /\ aff_dim f1 = &2 /\
           f2 face_of std_cube /\ aff_dim f2 = &2
           ==> f1 congruent f2`;;

let OCTAHEDRON_CONGRUENT_EDGES = `!e1 e2. e1 face_of std_octahedron /\ aff_dim e1 = &1 /\
           e2 face_of std_octahedron /\ aff_dim e2 = &1
           ==> e1 congruent e2`;;

let OCTAHEDRON_CONGRUENT_FACETS = `!f1 f2. f1 face_of std_octahedron /\ aff_dim f1 = &2 /\
           f2 face_of std_octahedron /\ aff_dim f2 = &2
           ==> f1 congruent f2`;;

let DODECAHEDRON_CONGRUENT_EDGES = `!e1 e2. e1 face_of std_dodecahedron /\ aff_dim e1 = &1 /\
           e2 face_of std_dodecahedron /\ aff_dim e2 = &1
           ==> e1 congruent e2`;;

let DODECAHEDRON_CONGRUENT_FACETS = `!f1 f2. f1 face_of std_dodecahedron /\ aff_dim f1 = &2 /\
           f2 face_of std_dodecahedron /\ aff_dim f2 = &2
           ==> f1 congruent f2`;;

let ICOSAHEDRON_CONGRUENT_EDGES = `!e1 e2. e1 face_of std_icosahedron /\ aff_dim e1 = &1 /\
           e2 face_of std_icosahedron /\ aff_dim e2 = &1
           ==> e1 congruent e2`;;

let ICOSAHEDRON_CONGRUENT_FACETS = `!f1 f2. f1 face_of std_icosahedron /\ aff_dim f1 = &2 /\
           f2 face_of std_icosahedron /\ aff_dim f2 = &2
           ==> f1 congruent f2`;;
