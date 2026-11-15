;; Statement-only formalization of PutnamBench corpus artifact putnam_1971_a3:
;; the product of the three side lengths of a lattice triangle on a circle
;; is at least twice the positive circle radius. This file contains no proof.

(in-package "ACL2")

;; ACL2 represents the positive radius R by the exact rational value R^2 and
;; replaces each Euclidean distance by its square.  The conclusion below is
;; therefore exactly the square of
;;
;;   distance(A,B) * distance(A,C) * distance(B,C) >= 2 * R;
;;
;; both sides of the source inequality are nonnegative, so the two conclusions
;; are bidirectionally equivalent.
;;
;; This does not restrict the source's real circle-center witness.  For three
;; distinct lattice points on a positive-radius circle, subtracting pairs of
;; circle equations gives two independent linear equations with integer
;; coefficients.  Hence the unique real center has rational coordinates, and
;; then R^2 is rational.  Conversely, every positive rational radius-square
;; and rational center satisfying the equations below embeds in the reals,
;; with source radius sqrt(R^2).  The center remains internally existential.

(defun putnam-1971-a3-square (x)
  (* x x))

(defun putnam-1971-a3-distance-squared
    (left-x left-y right-x right-y)
  (+ (putnam-1971-a3-square (- left-x right-x))
     (putnam-1971-a3-square (- left-y right-y))))

(defun-sk putnam-1971-a3-on-common-circle-p
    (a-x a-y b-x b-y c-x c-y radius-squared)
  (exists (center-x center-y)
    (and
     (rationalp center-x)
     (rationalp center-y)
     (equal
      (putnam-1971-a3-distance-squared
       a-x a-y center-x center-y)
      radius-squared)
     (equal
      (putnam-1971-a3-distance-squared
       b-x b-y center-x center-y)
      radius-squared)
     (equal
      (putnam-1971-a3-distance-squared
       c-x c-y center-x center-y)
      radius-squared))))

(defun putnambench-putnam-1971-a3-statement
    (a-x a-y b-x b-y c-x c-y radius-squared)
  (let
      ((ab-squared
        (putnam-1971-a3-distance-squared a-x a-y b-x b-y))
       (ac-squared
        (putnam-1971-a3-distance-squared a-x a-y c-x c-y))
       (bc-squared
        (putnam-1971-a3-distance-squared b-x b-y c-x c-y)))
    (implies
     (and
      (integerp a-x)
      (integerp a-y)
      (integerp b-x)
      (integerp b-y)
      (integerp c-x)
      (integerp c-y)
      (not (and (equal a-x b-x) (equal a-y b-y)))
      (not (and (equal a-x c-x) (equal a-y c-y)))
      (not (and (equal b-x c-x) (equal b-y c-y)))
      (rationalp radius-squared)
      (< 0 radius-squared)
      (putnam-1971-a3-on-common-circle-p
       a-x a-y b-x b-y c-x c-y radius-squared))
     (<= (* 4 radius-squared)
         (* ab-squared ac-squared bc-squared)))))

(value-triple :itpeval-statement-checked)
:q
