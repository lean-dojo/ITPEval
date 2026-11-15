(* ========================================================================= *)
(* #64: L'Hopital's rule.                                                    *)
(* ========================================================================= *)

needs "Library/analysis.ml";;

override_interface ("-->",`(tends_real_real)`);;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Cauchy mean value theorem.                                                *)
(* ------------------------------------------------------------------------- *)

let MVT2 = `!f g a b.
        a < b /\
        (!x. a <= x /\ x <= b ==> f contl x /\ g contl x) /\
        (!x. a < x /\ x < b ==> f differentiable x /\ g differentiable x)
        ==> ?z f' g'. a < z /\ z < b /\ (f diffl f') z /\ (g diffl g') z /\
                      (f b - f a) * g' = (g b - g a) * f'`;;

(* ------------------------------------------------------------------------- *)
(* First, assume f and g actually take value zero at c.                      *)
(* ------------------------------------------------------------------------- *)

let LHOPITAL_WEAK = `!f g f' g' c L d.
        &0 < d /\
        (!x. &0 < abs(x - c) /\ abs(x - c) < d
             ==> (f diffl f'(x)) x /\ (g diffl g'(x)) x /\ ~(g'(x) = &0)) /\
        f(c) = &0 /\ g(c) = &0 /\ (f --> &0) c /\ (g --> &0) c /\
        ((\x. f'(x) / g'(x)) --> L) c
        ==> ((\x. f(x) / g(x)) --> L) c`;;

(* ------------------------------------------------------------------------- *)
(* Now generalize by continuity extension.                                   *)
(* ------------------------------------------------------------------------- *)

let LHOPITAL = `!f g f' g' c L d.
        &0 < d /\
        (!x. &0 < abs(x - c) /\ abs(x - c) < d
             ==> (f diffl f'(x)) x /\ (g diffl g'(x)) x /\ ~(g'(x) = &0)) /\
        (f --> &0) c /\ (g --> &0) c /\ ((\x. f'(x) / g'(x)) --> L) c
        ==> ((\x. f(x) / g(x)) --> L) c`;;
