;; Statement-only formalization of PutnamBench artifact putnam_1962_a3:
;; the area ratio for the triangle formed by pairwise intersections of three
;; cevians whose opposite-side division ratios share a positive constant k.
;; This file contains no proof.

(in-package "ACL2")

;; ACL2's exact rational plane is bidirectionally equivalent to the source
;; theorem over the real plane. For k > 0 and noncollinear A, B, C, the three
;; side conditions uniquely give
;;   A' = (k B + C)/(k+1), B' = (k C + A)/(k+1),
;;   C' = (k A + B)/(k+1).
;; The pairwise cevian intersections are then unique rational functions of
;; A, B, C, and k, with nonzero denominators k+1 and k^2+k+1. Consequently
;; every real configuration in the hypotheses belongs to this continuous
;; rationally parameterized family. A real counterexample would persist after
;; a small perturbation of A, B, C, and k and hence yield a rational
;; counterexample; conversely every rational configuration is real.

(defun putnam-1962-a3-point-p (point)
  (and (consp point)
       (rationalp (car point))
       (rationalp (cdr point))))

(defun putnam-1962-a3-square (x)
  (* x x))

(defun putnam-1962-a3-orientation (a b c)
  (- (* (- (car b) (car a))
        (- (cdr c) (cdr a)))
     (* (- (cdr b) (cdr a))
        (- (car c) (car a)))))

(defun putnam-1962-a3-distance-squared (a b)
  (+ (putnam-1962-a3-square (- (car b) (car a)))
     (putnam-1962-a3-square (- (cdr b) (cdr a)))))

;; For collinear points, (P-A) dot (P-B) <= 0 is exactly P in [A,B].
(defun putnam-1962-a3-closed-segment-p (p a b)
  (and (equal (putnam-1962-a3-orientation a b p) 0)
       (<= (+ (* (- (car p) (car a))
                  (- (car p) (car b)))
               (* (- (cdr p) (cdr a))
                  (- (cdr p) (cdr b))))
           0)))

(defun putnambench-putnam-1962-a3-statement
    (a b c a-prime b-prime c-prime p q r k)
  (implies
   (and
    (putnam-1962-a3-point-p a)
    (putnam-1962-a3-point-p b)
    (putnam-1962-a3-point-p c)
    (putnam-1962-a3-point-p a-prime)
    (putnam-1962-a3-point-p b-prime)
    (putnam-1962-a3-point-p c-prime)
    (putnam-1962-a3-point-p p)
    (putnam-1962-a3-point-p q)
    (putnam-1962-a3-point-p r)
    (rationalp k)
    (< 0 k)
    (not (equal (putnam-1962-a3-orientation a b c) 0))
    (putnam-1962-a3-closed-segment-p a-prime b c)
    (equal
     (putnam-1962-a3-distance-squared c a-prime)
     (* k k
        (putnam-1962-a3-distance-squared a-prime b)))
    (putnam-1962-a3-closed-segment-p b-prime c a)
    (equal
     (putnam-1962-a3-distance-squared a b-prime)
     (* k k
        (putnam-1962-a3-distance-squared b-prime c)))
    (putnam-1962-a3-closed-segment-p c-prime a b)
    (equal
     (putnam-1962-a3-distance-squared b c-prime)
     (* k k
        (putnam-1962-a3-distance-squared c-prime a)))
    (putnam-1962-a3-closed-segment-p p b b-prime)
    (putnam-1962-a3-closed-segment-p p c c-prime)
    (putnam-1962-a3-closed-segment-p q c c-prime)
    (putnam-1962-a3-closed-segment-p q a a-prime)
    (putnam-1962-a3-closed-segment-p r a a-prime)
    (putnam-1962-a3-closed-segment-p r b b-prime))
   ;; A triangle's planar Lebesgue area is half the absolute orientation.
   ;; Both source denominators are positive, so this is the cross-multiplied
   ;; form of the stated area-ratio equality.
   (equal
    (* (abs (putnam-1962-a3-orientation p q r))
       (+ (* k k) k 1))
    (* (abs (putnam-1962-a3-orientation a b c))
       (putnam-1962-a3-square (- k 1))))))

(value-triple :itpeval-statement-checked)
:q
