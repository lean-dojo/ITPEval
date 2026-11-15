(* ========================================================================= *)
(* Area of a circle.                                                         *)
(* ========================================================================= *)

needs "Multivariate/measure.ml";;
needs "Multivariate/realanalysis.ml";;

(* ------------------------------------------------------------------------- *)
(* Circle area. Should maybe extend WLOG tactics for such scaling.           *)
(* ------------------------------------------------------------------------- *)

let AREA_UNIT_CBALL = `measure(cball(vec 0:real^2,&1)) = pi`;;

let AREA_CBALL = `!z:real^2 r. &0 <= r ==> measure(cball(z,r)) = pi * r pow 2`;;

let AREA_BALL = `!z:real^2 r. &0 <= r ==> measure(ball(z,r)) = pi * r pow 2`;;

(* ------------------------------------------------------------------------- *)
(* Volume of a ball too, just for fun.                                       *)
(* ------------------------------------------------------------------------- *)

let VOLUME_CBALL = `!z:real^3 r. &0 <= r ==> measure(cball(z,r)) = &4 / &3 * pi * r pow 3`;;

let VOLUME_BALL = `!z:real^3 r. &0 <= r ==> measure(ball(z,r)) =  &4 / &3 * pi * r pow 3`;;
