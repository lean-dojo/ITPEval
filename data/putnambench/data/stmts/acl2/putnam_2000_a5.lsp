;; Statement-only formalization of PutnamBench corpus artifact putnam_2000_a5:
;; among three distinct lattice points on a positive-radius circle, two are
;; separated by at least the cube root of the radius. This file contains no
;; proof.

(in-package "ACL2")

;; Let D be the determinant of the two edge vectors from P0. Three distinct
;; points lie on a positive-radius circle exactly when D is nonzero. In that
;; case the circle is unique, its center has rational coordinates, and
;;
;;   r^2 = (d01 * d02 * d12) / (4 * D^2),
;;
;; where dij is the squared distance between Pi and Pj. Thus eliminating the
;; source's real center and positive radius does not restrict its instances.
;; Since distances and r are nonnegative,
;;
;;   dist(Pi,Pj) >= r^(1/3)
;;
;; is bidirectionally equivalent, after squaring and cubing, to
;;
;;   4 * D^2 * dij^3 >= d01 * d02 * d12.
;;
;; The disjunction below ranges over all three unordered pairs, exactly
;; encoding the source's existential conclusion without square or cube roots.

(defun putnam-2000-a5-distance-squared (left-x left-y right-x right-y)
  (+ (* (- left-x right-x) (- left-x right-x))
     (* (- left-y right-y) (- left-y right-y))))

(defun putnam-2000-a5-determinant (x0 y0 x1 y1 x2 y2)
  (- (* (- x1 x0) (- y2 y0))
     (* (- y1 y0) (- x2 x0))))

(defun putnam-2000-a5-pair-bound-p
    (distance-squared determinant-squared side-product)
  (<= side-product
      (* 4
         determinant-squared
         distance-squared
         distance-squared
         distance-squared)))

(defun putnambench-putnam-2000-a5-statement
    (x0 y0 x1 y1 x2 y2)
  (let* ((d01 (putnam-2000-a5-distance-squared x0 y0 x1 y1))
         (d02 (putnam-2000-a5-distance-squared x0 y0 x2 y2))
         (d12 (putnam-2000-a5-distance-squared x1 y1 x2 y2))
         (determinant
          (putnam-2000-a5-determinant x0 y0 x1 y1 x2 y2))
         (determinant-squared (* determinant determinant))
         (side-product (* d01 d02 d12)))
    (implies
     (and
      (integerp x0)
      (integerp y0)
      (integerp x1)
      (integerp y1)
      (integerp x2)
      (integerp y2)
      (not (and (equal x0 x1) (equal y0 y1)))
      (not (and (equal x0 x2) (equal y0 y2)))
      (not (and (equal x1 x2) (equal y1 y2)))
      (not (equal determinant 0)))
     (or
      (putnam-2000-a5-pair-bound-p
       d01 determinant-squared side-product)
      (putnam-2000-a5-pair-bound-p
       d02 determinant-squared side-product)
      (putnam-2000-a5-pair-bound-p
       d12 determinant-squared side-product)))))

(value-triple :itpeval-statement-checked)
:q
