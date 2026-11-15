(* ========================================================================= *)
(* The isoperimetric inequality.                                             *)
(* ========================================================================= *)

needs "Multivariate/cauchy.ml";;
needs "Multivariate/lpspaces.ml";;
needs "100/green.ml";;

(* ------------------------------------------------------------------------- *)
(* A few lemmas to switch between views of a convex curve.                   *)
(* ------------------------------------------------------------------------- *)

let lemma1 = `!g:real^1->real^2.
        simple_path g /\ pathfinish g = pathstart g /\
        convex(inside(path_image g))
        ==> convex hull (path_image g) = closure(inside(path_image g))`;;

let lemma2 = `!g:real^1->real^2.
        simple_path g /\ pathfinish g = pathstart g /\
        convex(inside(path_image g))
        ==> frontier(convex hull (path_image g)) = path_image g`;;

let lemma3 = `!g:real^1->real^2.
        simple_path g /\
        pathfinish g = pathstart g /\
        path_image g SUBSET frontier (convex hull path_image g)
        ==> frontier (convex hull path_image g) = path_image g`;;

(* ------------------------------------------------------------------------- *)
(* Part 1: The Wirtinger inequality.                                         *)
(* ------------------------------------------------------------------------- *)

let REAL_HOELDER_BOUND_2 = `!f s. real_measurable s /\
         f real_measurable_on s /\
         (\x. f x pow 2) real_integrable_on s
         ==> (real_integral s f) pow 2
             <= real_measure s * real_integral s (\x. f x pow 2)`;;

let WIRTINGER_INEQUALITY = `!f f'.
        (!x. x IN real_interval[&0,&2 * pi]
             ==> (f' has_real_integral (f x - f(&0))) (real_interval[&0,x])) /\
        f(&2 * pi) = f(&0) /\
        (f has_real_integral &0) (real_interval[&0,&2 * pi]) /\
        (\x. f'(x) pow 2) real_integrable_on real_interval[&0,&2 * pi]
        ==> (\x. f(x) pow 2) real_integrable_on real_interval[&0,&2 * pi] /\
            real_integral (real_interval[&0,&2 * pi]) (\x. f(x) pow 2) <=
            real_integral (real_interval[&0,&2 * pi]) (\x. f'(x) pow 2) /\
            (real_integral (real_interval[&0,&2 * pi]) (\x. f(x) pow 2) =
             real_integral (real_interval[&0,&2 * pi]) (\x. f'(x) pow 2)
             ==> ?c a. !x. x IN real_interval[&0,&2 * pi]
                           ==> f x = c * sin(x - a))`;;

let SCALED_WIRTINGER_INEQUALITY = `!f f'.
      (!x. x IN real_interval[&0,&1]
           ==> (f' has_real_integral (f x - f(&0))) (real_interval[&0,x])) /\
      f(&1) = f(&0) /\
      (f has_real_integral &0) (real_interval[&0,&1]) /\
      (\x. f'(x) pow 2) real_integrable_on real_interval[&0,&1]
      ==> (\x. f(x) pow 2) real_integrable_on real_interval[&0,&1] /\
          real_integral (real_interval[&0,&1]) (\x. (&2 * pi * f(x)) pow 2) <=
          real_integral (real_interval[&0,&1]) (\x. f'(x) pow 2) /\
          (real_integral (real_interval[&0,&1]) (\x. (&2 * pi * f(x)) pow 2) =
           real_integral (real_interval[&0,&1]) (\x. f'(x) pow 2)
           ==> ?c a. !x. x IN real_interval[&0,&1]
                         ==> f x = c * sin(&2 * pi * x - a))`;;

(* ------------------------------------------------------------------------- *)
(* Part 2: a very special case of Green's theorem for a convex area.         *)
(* ------------------------------------------------------------------------- *)

let GREEN_AREA_THEOREM = `!(g:real^1->real^2) g' u a.
        simple_path g /\ pathstart g = a /\ pathfinish g = a /\
        g absolutely_continuous_on interval[vec 0,vec 1] /\
        negligible u /\
        (!t. t IN interval[vec 0,vec 1] DIFF u
             ==> (g has_vector_derivative g'(t)) (at t))
        ==> (\t. lift(g'(t)$1 * g(t)$2)) integrable_on
            interval[vec 0,vec 1] /\
            norm(integral (interval[vec 0,vec 1])
                          (\t. lift(g'(t)$1 * g(t)$2))) =
            measure(inside(path_image g))`;;

(* ------------------------------------------------------------------------- *)
(* Part 3: Isoperimetric theorem for a convex curve.                         *)
(* ------------------------------------------------------------------------- *)

let ISOPERIMETRIC_THEOREM_CONVEX = `!L g:real^1->real^2.
        rectifiable_path g /\
        simple_path g /\
        pathfinish g = pathstart g /\
        convex(inside(path_image g)) /\
        path_length g = L
        ==> measure(inside(path_image g)) <= L pow 2 / (&4 * pi) /\
            (measure(inside(path_image g)) =  L pow 2 / (&4 * pi)
             ==> ?a r. path_image g = sphere(a,r))`;;

(* ------------------------------------------------------------------------- *)
(* Part 4: Convexification of an arbitrary rectifiable simple curve.         *)
(* ------------------------------------------------------------------------- *)

let STEP_LEMMA = `!g:real^1->real^2 a b L.
        simple_path g /\ pathfinish g = pathstart g /\
        (!x y. x IN interval [vec 0,vec 1] /\
               y IN interval [vec 0,vec 1]
               ==> dist(g x,g y) <= L * dist(x,y)) /\
        drop a < drop b /\
        a IN interval[vec 0,vec 1] /\ b IN interval[vec 0,vec 1] /\
        g(a) IN frontier(convex hull (path_image g)) /\
        g(b) IN frontier(convex hull (path_image g)) /\
        IMAGE g (interval(a,b)) INTER frontier(convex hull (path_image g)) = {}
        ==> ?h. simple_path h /\
                pathstart h = pathstart g /\ pathfinish h = pathstart g /\
                (!x y. x IN interval [vec 0,vec 1] /\
                       y IN interval [vec 0,vec 1]
                       ==> dist(h x,h y) <= L * dist(x,y)) /\
                path_length h < path_length g /\
                convex hull (path_image h) = convex hull (path_image g) /\
                (!x. ~(x IN interval(a,b)) ==> h x = g x) /\
                IMAGE h (interval[a,b]) SUBSET
                frontier(convex hull (path_image g))`;;

let ISOPERIMETRIC_CONVEXIFICATION = `!g:real^1->real^2.
        rectifiable_path g /\
        simple_path g /\
        pathfinish g = pathstart g
        ==> ?h:real^1->real^2.
                rectifiable_path h /\
                simple_path h /\
                pathfinish h = pathstart h /\
                path_length h <= path_length g /\
                convex hull (path_image h) = convex hull (path_image g) /\
                path_image h = frontier(convex hull (path_image g))`;;

let ISOPERIMETRIC_CONVEXIFICATION_1 = `!g:real^1->real^2.
        rectifiable_path g /\
        simple_path g /\
        pathfinish g = pathstart g /\
        ~convex(inside(path_image g))
        ==> ?h:real^1->real^2.
                rectifiable_path h /\
                simple_path h /\
                pathfinish h = pathstart h /\
                path_length h <= path_length g /\
                convex hull path_image h = convex hull path_image g /\
                path_image h = frontier (convex hull path_image g) /\
                measure(inside(path_image g)) < measure(inside(path_image h))`;;

(* ------------------------------------------------------------------------- *)
(* The grand finale.                                                         *)
(* ------------------------------------------------------------------------- *)

let ISOPERIMETRIC_THEOREM = `!L g:real^1->real^2.
        rectifiable_path g /\
        simple_path g /\
        pathfinish g = pathstart g /\
        path_length g = L
        ==> measure(inside(path_image g)) <= L pow 2 / (&4 * pi) /\
            (measure(inside(path_image g)) =  L pow 2 / (&4 * pi)
             ==> ?a r. path_image g = sphere(a,r))`;;
