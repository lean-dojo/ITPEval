(* ========================================================================= *)
(* Formalization of Jim Lawrence's proof of Euler's relation.                *)
(* ========================================================================= *)

needs "Multivariate/polytope.ml";;
needs "Library/binomial.ml";;
needs "100/inclusion_exclusion.ml";;
needs "100/combinations.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Interpret which "side" of a hyperplane a point is on.                     *)
(* ------------------------------------------------------------------------- *)

let hyperplane_side = new_definition
 `hyperplane_side (a,b) (x:real^N) = real_sgn (a dot x - b)`;;

(* ------------------------------------------------------------------------- *)
(* Equivalence relation imposed by a hyperplane arrangement.                 *)
(* ------------------------------------------------------------------------- *)

let hyperplane_equiv = new_definition
 `hyperplane_equiv A x y <=>
        !h. h IN A ==> hyperplane_side h x = hyperplane_side h y`;;

let HYPERPLANE_EQUIV_REFL = `!A x. hyperplane_equiv A x x`;;

let HYPERPLANE_EQUIV_SYM = `!A x y. hyperplane_equiv A x y <=> hyperplane_equiv A y x`;;

let HYPERPLANE_EQUIV_TRANS = `!A x y z.
        hyperplane_equiv A x y /\ hyperplane_equiv A y z
        ==> hyperplane_equiv A x z`;;

let HYPERPLANE_EQUIV_UNION = `!A B x y. hyperplane_equiv (A UNION B) x y <=>
                hyperplane_equiv A x y /\ hyperplane_equiv B x y`;;

(* ------------------------------------------------------------------------- *)
(* Cells of a hyperplane arrangement.                                        *)
(* ------------------------------------------------------------------------- *)

let hyperplane_cell = new_definition
 `hyperplane_cell A c <=> ?x. c = hyperplane_equiv A x`;;

let HYPERPLANE_CELL = `hyperplane_cell A c <=> ?x. c = {y | hyperplane_equiv A x y}`;;

let NOT_HYPERPLANE_CELL_EMPTY = `!A. ~(hyperplane_cell A {})`;;

let NONEMPTY_HYPERPLANE_CELL = `!A c. hyperplane_cell A c ==> ~(c = {})`;;

let UNIONS_HYPERPLANE_CELLS = `!A. UNIONS {c | hyperplane_cell A c} = (:real^N)`;;

let DISJOINT_HYPERPLANE_CELLS = `!A c1 c2. hyperplane_cell A c1 /\ hyperplane_cell A c2 /\ ~(c1 = c2)
             ==> DISJOINT c1 c2`;;

let DISJOINT_HYPERPLANE_CELLS_EQ = `!A c1 c2. hyperplane_cell A c1 /\ hyperplane_cell A c2
             ==> (DISJOINT c1 c2 <=> ~(c1 = c2))`;;

let HYPERPLANE_CELL_EMPTY = `hyperplane_cell {} c <=> c = (:real^N)`;;

let HYPERPLANE_CELL_SING_CASES = `!a b c:real^N->bool.
        hyperplane_cell {(a,b)} c
        ==>  c = {x | a dot x = b} \/
             c = {x | a dot x < b} \/
             c = {x | a dot x > b}`;;

let HYPERPLANE_CELL_SING = `!a b c.
        hyperplane_cell {(a,b)} c <=>
        if a = vec 0 then c = (:real^N)
        else c = {x | a dot x = b} \/
             c = {x | a dot x < b} \/
             c = {x | a dot x > b}`;;

let HYPERPLANE_CELL_UNION = `!A B c:real^N->bool.
        hyperplane_cell (A UNION B) c <=>
        ~(c = {}) /\
        ?c1 c2. hyperplane_cell A c1 /\
                hyperplane_cell B c2 /\
                c = c1 INTER c2`;;

let FINITE_HYPERPLANE_CELLS = `!A. FINITE A ==> FINITE {c:real^N->bool | hyperplane_cell A c}`;;

let FINITE_RESTRICT_HYPERPLANE_CELLS = `!P A. FINITE A ==> FINITE {c:real^N->bool | hyperplane_cell A c /\ P c}`;;

let FINITE_SET_OF_HYPERPLANE_CELLS = `!A C. FINITE A /\ (!c:real^N->bool. c IN C ==> hyperplane_cell A c)
         ==> FINITE C`;;

let PAIRWISE_DISJOINT_HYPERPLANE_CELLS = `!A C. (!c. c IN C ==> hyperplane_cell A c)
         ==> pairwise DISJOINT C`;;

let HYPERPLANE_CELL_INTER_OPEN_AFFINE = `!A c:real^N->bool.
        FINITE A /\ hyperplane_cell A c
        ==> ?s t. open s /\ affine t /\ c = s INTER t`;;

let HYPERPLANE_CELL_RELATIVELY_OPEN = `!A c:real^N->bool.
        FINITE A /\ hyperplane_cell A c
        ==> open_in (subtopology euclidean (affine hull c)) c`;;

let HYPERPLANE_CELL_RELATIVE_INTERIOR = `!A c:real^N->bool.
        FINITE A /\ hyperplane_cell A c
        ==> relative_interior c = c`;;

let HYPERPLANE_CELL_CONVEX = `!A c:real^N->bool. hyperplane_cell A c ==> convex c`;;

let HYPERPLANE_CELL_INTERS = `!A C. (!c:real^N->bool. c IN C ==> hyperplane_cell A c) /\
         ~(C = {}) /\ ~(INTERS C = {})
         ==> hyperplane_cell A (INTERS C)`;;

let HYPERPLANE_CELL_INTER = `!A s t:real^N->bool.
        hyperplane_cell A s /\ hyperplane_cell A t /\ ~(s INTER t = {})
        ==> hyperplane_cell A (s INTER t)`;;

(* ------------------------------------------------------------------------- *)
(* A cell complex is considered to be a union of such cells.                 *)
(* ------------------------------------------------------------------------- *)

let hyperplane_cellcomplex = new_definition
 `hyperplane_cellcomplex A s <=>
        ?t. (!c. c IN t ==> hyperplane_cell A c) /\
            s = UNIONS t`;;

let HYPERPLANE_CELLCOMPLEX_EMPTY = `!A:real^N#real->bool. hyperplane_cellcomplex A {}`;;

let HYPERPLANE_CELL_CELLCOMPLEX = `!A c:real^N->bool. hyperplane_cell A c ==> hyperplane_cellcomplex A c`;;

let HYPERPLANE_CELLCOMPLEX_UNIONS = `!A C. (!s:real^N->bool. s IN C ==> hyperplane_cellcomplex A s)
         ==> hyperplane_cellcomplex A (UNIONS C)`;;

let HYPERPLANE_CELLCOMPLEX_UNION = `!A s t.
        hyperplane_cellcomplex A s /\ hyperplane_cellcomplex A t
        ==> hyperplane_cellcomplex A (s UNION t)`;;

let HYPERPLANE_CELLCOMPLEX_UNIV = `!A. hyperplane_cellcomplex A (:real^N)`;;

let HYPERPLANE_CELLCOMPLEX_INTERS = `!A C. (!s:real^N->bool. s IN C ==> hyperplane_cellcomplex A s)
         ==> hyperplane_cellcomplex A (INTERS C)`;;

let HYPERPLANE_CELLCOMPLEX_INTER = `!A s t.
        hyperplane_cellcomplex A s /\ hyperplane_cellcomplex A t
        ==> hyperplane_cellcomplex A (s INTER t)`;;

let HYPERPLANE_CELLCOMPLEX_COMPL = `!A s. hyperplane_cellcomplex A s
         ==> hyperplane_cellcomplex A ((:real^N) DIFF s)`;;

let HYPERPLANE_CELLCOMPLEX_DIFF = `!A s t.
        hyperplane_cellcomplex A s /\ hyperplane_cellcomplex A t
        ==> hyperplane_cellcomplex A (s DIFF t)`;;

let HYPERPLANE_CELLCOMPLEX_MONO = `!A B s:real^N->bool.
        hyperplane_cellcomplex A s /\ A SUBSET B
        ==> hyperplane_cellcomplex B s`;;

let FINITE_HYPERPLANE_CELLCOMPLEXES = `!A. FINITE A ==> FINITE {c:real^N->bool | hyperplane_cellcomplex A c}`;;

let FINITE_RESTRICT_HYPERPLANE_CELLCOMPLEXES = `!P A. FINITE A
         ==> FINITE {c:real^N->bool | hyperplane_cellcomplex A c /\ P c}`;;

let FINITE_SET_OF_HYPERPLANE_CELLS = `!A C. FINITE A /\ (!c:real^N->bool. c IN C ==> hyperplane_cellcomplex A c)
         ==> FINITE C`;;

let CELL_SUBSET_CELLCOMPLEX = `!A s c:real^N->bool.
        hyperplane_cell A c /\ hyperplane_cellcomplex A s
        ==> (c SUBSET s <=> ~(DISJOINT c s))`;;

(* ------------------------------------------------------------------------- *)
(* Euler characteristic.                                                     *)
(* ------------------------------------------------------------------------- *)

let euler_characteristic = new_definition
 `euler_characteristic A (s:real^N->bool) =
        sum {c | hyperplane_cell A c /\ c SUBSET s}
            (\c. (-- &1) pow (num_of_int(aff_dim c)))`;;

let EULER_CHARACTERISTIC_EMPTY = `euler_characteristic A {} = &0`;;

let EULER_CHARACTERISTIC_CELL_UNIONS = `!A C. (!c:real^N->bool. c IN C ==> hyperplane_cell A c)
         ==> euler_characteristic A (UNIONS C) =
             sum C (\c. (-- &1) pow (num_of_int(aff_dim c)))`;;

let EULER_CHARACTERISTIC_CELL = `!A c. hyperplane_cell A c
         ==> euler_characteristic A c =  (-- &1) pow (num_of_int(aff_dim c))`;;

let EULER_CHARACTERISTIC_CELLCOMPLEX_UNION = `!A s t:real^N->bool.
        FINITE A /\
        hyperplane_cellcomplex A s /\
        hyperplane_cellcomplex A t /\
        DISJOINT s t
        ==> euler_characteristic A (s UNION t) =
            euler_characteristic A s + euler_characteristic A t`;;

let EULER_CHARACTERISTIC_CELLCOMPLEX_UNIONS = `!A C. FINITE A /\
         (!c:real^N->bool. c IN C ==> hyperplane_cellcomplex A c) /\
         pairwise DISJOINT C
         ==> euler_characteristic A (UNIONS C) =
             sum C (\c. euler_characteristic A c)`;;

let EULER_CHARACTERISTIC = `!A s:real^N->bool.
        FINITE A
        ==> euler_characteristic A s =
            sum (0..dimindex(:N))
                (\d. (-- &1) pow d *
                     &(CARD {c | hyperplane_cell A c /\ c SUBSET s /\
                                 aff_dim c = &d}))`;;

(* ------------------------------------------------------------------------- *)
(* Show that the characteristic is invariant w.r.t. hyperplane arrangement.  *)
(* ------------------------------------------------------------------------- *)

let HYPERPLANE_CELLS_DISTINCT_LEMMA = `!a b. {x | a dot x = b} INTER {x | a dot x < b} = {} /\
         {x | a dot x = b} INTER {x | a dot x > b} = {} /\
         {x | a dot x < b} INTER {x | a dot x = b} = {} /\
         {x | a dot x < b} INTER {x | a dot x > b} = {} /\
         {x | a dot x > b} INTER {x | a dot x = b} = {} /\
         {x | a dot x > b} INTER {x | a dot x < b} = {}`;;

let EULER_CHARACTERSTIC_LEMMA = `!A h s:real^N->bool.
        FINITE A /\ hyperplane_cellcomplex A s
        ==> euler_characteristic (h INSERT A) s = euler_characteristic A s`;;

let EULER_CHARACTERSTIC_INVARIANT = `!A B h s:real^N->bool.
        FINITE A /\ FINITE B /\
        hyperplane_cellcomplex A s /\ hyperplane_cellcomplex B s
        ==> euler_characteristic A s = euler_characteristic B s`;;

let EULER_CHARACTERISTIC_INCLUSION_EXCLUSION = `!A s:(real^N->bool)->bool.
        FINITE A /\ FINITE s /\ (!k. k IN s ==> hyperplane_cellcomplex A k)
        ==> euler_characteristic A (UNIONS s) =
            sum {t | t SUBSET s /\ ~(t = {})}
                (\t. (-- &1) pow (CARD t + 1) *
                     euler_characteristic A (INTERS t))`;;

(* ------------------------------------------------------------------------- *)
(* Euler-type relation for full-dimensional proper polyhedral cones.         *)
(* ------------------------------------------------------------------------- *)

let EULER_POLYHEDRAL_CONE = `!s. polyhedron s /\ conic s /\ ~(interior s = {}) /\ ~(s = (:real^N))
       ==> sum (0..dimindex(:N))
               (\d. (-- &1) pow d *
                    &(CARD {f | f face_of s /\ aff_dim f = &d })) = &0`;;

(* ------------------------------------------------------------------------- *)
(* Euler-Poincare relation for special (n-1)-dimensional polytope.           *)
(* ------------------------------------------------------------------------- *)

let EULER_POINCARE_LEMMA = `!p:real^N->bool.
        2 <= dimindex(:N) /\ polytope p /\ affine hull p = {x | x$1 = &1}
        ==> sum (0..dimindex(:N)-1)
               (\d. (-- &1) pow d *
                    &(CARD {f | f face_of p /\ aff_dim f = &d })) = &1`;;

let EULER_POINCARE_SPECIAL = `!p:real^N->bool.
        2 <= dimindex(:N) /\ polytope p /\ affine hull p = {x | x$1 = &0}
        ==> sum (0..dimindex(:N)-1)
               (\d. (-- &1) pow d *
                    &(CARD {f | f face_of p /\ aff_dim f = &d })) = &1`;;

(* ------------------------------------------------------------------------- *)
(* Now Euler-Poincare for a general full-dimensional polytope.               *)
(* ------------------------------------------------------------------------- *)

let EULER_POINCARE_FULL = `!p:real^N->bool.
        polytope p /\ aff_dim p = &(dimindex(:N))
        ==> sum (0..dimindex(:N))
                (\d. (-- &1) pow d *
                     &(CARD {f | f face_of p /\ aff_dim f = &d })) = &1`;;

(* ------------------------------------------------------------------------- *)
(* In particular the Euler relation in 3D.                                   *)
(* ------------------------------------------------------------------------- *)

let EULER_RELATION = `!p:real^3->bool.
        polytope p /\ aff_dim p = &3
        ==> (CARD {v | v face_of p /\ aff_dim(v) = &0} +
             CARD {f | f face_of p /\ aff_dim(f) = &2}) -
            CARD {e | e face_of p /\ aff_dim(e) = &1} = 2`;;
