(* ========================================================================= *)
(* Feuerbach's theorem.                                                      *)
(* ========================================================================= *)

needs "Multivariate/convex.ml";;

(* ------------------------------------------------------------------------- *)
(* Algebraic condition for two circles to be tangent to each other.          *)
(* ------------------------------------------------------------------------- *)

let CIRCLES_TANGENT = `!r1 r2 c1 c2.
        &0 <= r1 /\ &0 <= r2 /\
        (dist(c1,c2) = r1 + r2 \/ dist(c1,c2) = abs(r1 - r2))
        ==> c1 = c2 /\ r1 = r2 \/
            ?!x:real^2. dist(c1,x) = r1 /\ dist(c2,x) = r2`;;

(* ------------------------------------------------------------------------- *)
(*                       Feuerbach's theorem                                 *)
(*                                                                           *)
(* Given a non-degenerate triangle abc, let the circle passing through       *)
(* the midpoints of its sides (the "9 point circle") have center "ncenter"   *)
(* and radius "nradius". Now suppose the circle with center "icenter" and    *)
(* radius "iradius" is tangent to three sides (either internally or          *)
(* externally to one side and two produced sides), meaning that it's either  *)
(* the inscribed circle or one of the three escribed circles. Then the two   *)
(* circles are tangent to each other, i.e. either they are identical or they *)
(* touch at exactly one point.                                               *)
(* ------------------------------------------------------------------------- *)

let FEUERBACH = `!a b c mbc mac mab pbc pac pab ncenter icenter nradius iradius.
      ~(collinear {a,b,c}) /\
      midpoint(a,b) = mab /\
      midpoint(b,c) = mbc /\
      midpoint(c,a) = mac /\
      dist(ncenter,mbc) = nradius /\
      dist(ncenter,mac) = nradius /\
      dist(ncenter,mab) = nradius /\
      dist(icenter,pbc) = iradius /\
      dist(icenter,pac) = iradius /\
      dist(icenter,pab) = iradius /\
      collinear {a,b,pab} /\ orthogonal (a - b) (icenter - pab) /\
      collinear {b,c,pbc} /\ orthogonal (b - c) (icenter - pbc) /\
      collinear {a,c,pac} /\ orthogonal (a - c) (icenter - pac)
      ==> ncenter = icenter /\ nradius = iradius \/
          ?!x:real^2. dist(ncenter,x) = nradius /\ dist(icenter,x) = iradius`;;

(* ------------------------------------------------------------------------- *)
(* As a little bonus, verify that the circle passing through the             *)
(* midpoints of the sides is indeed a 9-point circle, i.e. it passes         *)
(* through the feet of the altitudes and the midpoints of the lines joining  *)
(* the vertices to the orthocenter (where the alititudes intersect).         *)
(* ------------------------------------------------------------------------- *)

let NINE_POINT_CIRCLE_1 = `!a b c:real^2 mbc mac mab fbc fac fab ncenter nradius.
      ~(collinear {a,b,c}) /\
      midpoint(a,b) = mab /\
      midpoint(b,c) = mbc /\
      midpoint(c,a) = mac /\
      dist(ncenter,mbc) = nradius /\
      dist(ncenter,mac) = nradius /\
      dist(ncenter,mab) = nradius /\
      collinear {a,b,fab} /\ orthogonal (a - b) (c - fab) /\
      collinear {b,c,fbc} /\ orthogonal (b - c) (a - fbc) /\
      collinear {c,a,fac} /\ orthogonal (c - a) (b - fac)
      ==> dist(ncenter,fab) = nradius /\
          dist(ncenter,fbc) = nradius /\
          dist(ncenter,fac) = nradius`;;

let NINE_POINT_CIRCLE_2 = `!a b c:real^2 mbc mac mab fbc fac fab ncenter nradius.
      ~(collinear {a,b,c}) /\
      midpoint(a,b) = mab /\
      midpoint(b,c) = mbc /\
      midpoint(c,a) = mac /\
      dist(ncenter,mbc) = nradius /\
      dist(ncenter,mac) = nradius /\
      dist(ncenter,mab) = nradius /\
      collinear {a,b,fab} /\ orthogonal (a - b) (c - fab) /\
      collinear {b,c,fbc} /\ orthogonal (b - c) (a - fbc) /\
      collinear {c,a,fac} /\ orthogonal (c - a) (b - fac) /\
      collinear {oc,a,fbc} /\ collinear {oc,b,fac} /\ collinear{oc,c,fab}
      ==> dist(ncenter,midpoint(oc,a)) = nradius /\
          dist(ncenter,midpoint(oc,b)) = nradius /\
          dist(ncenter,midpoint(oc,c)) = nradius`;;
