;; Statement-only formalization of PutnamBench corpus artifact putnam_2018_a6:
;; four plane points with no three collinear and with all six squared
;; distances rational have a rational ratio of the areas of triangles ABC
;; and ABD. This file contains no proof.

(in-package "ACL2")

;; The six arguments used below are squared distances. For squared side
;; lengths X, Y, Z, this expression is sixteen times the squared area of the
;; corresponding triangle.
(defun putnam-2018-a6-heron-sixteen (x y z)
  (- (* 4 x y)
     (* (- (+ x y) z)
        (- (+ x y) z))))

;; This is the determinant of twice the Gram matrix of the vectors AB, AC,
;; and AD. Its vanishing, together with a positive ABC Heron determinant,
;; says that the four-point metric is realized in a two-dimensional
;; Euclidean space.
(defun putnam-2018-a6-scaled-gram-determinant
    (ab ac ad bc bd cd)
  (let ((ab-ac (- (+ ab ac) bc))
        (ab-ad (- (+ ab ad) bd))
        (ac-ad (- (+ ac ad) cd)))
    (+ (* 2 ab
          (- (* 2 ac 2 ad)
             (* ac-ad ac-ad)))
       (* (- ab-ac)
          (- (* ab-ac 2 ad)
             (* ac-ad ab-ad)))
       (* ab-ad
          (- (* ab-ac ac-ad)
             (* 2 ac ab-ad))))))

;; A natural square root of N, when it exists, is at most N. Thus this
;; bounded search represents the existential square-root witness internally.
(defun putnam-2018-a6-square-through-p (n candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (and (natp n)
           (natp candidate))
      (or (equal (* candidate candidate) n)
          (and (not (zp candidate))
               (putnam-2018-a6-square-through-p
                n (- candidate 1))))
    nil))

;; ACL2 rationals are stored in lowest terms. A nonnegative rational has a
;; rational square root exactly when its numerator and denominator are both
;; perfect squares.
(defun putnam-2018-a6-rational-square-p (value)
  (and
   (rationalp value)
   (<= 0 value)
   (putnam-2018-a6-square-through-p
    (numerator value) (numerator value))
   (putnam-2018-a6-square-through-p
    (denominator value) (denominator value))))

;; Every source configuration determines six positive rational squared
;; distances satisfying the four positive Heron conditions and the zero Gram
;; determinant below. Conversely, these conditions make the leading 2-by-2
;; Gram block positive definite and the full Gram matrix positive semidefinite
;; of rank two, so they reconstruct a real plane configuration with exactly
;; the stated distances and with no three points collinear. Hence this
;; distance-geometry representation is bidirectionally equivalent to the
;; point-based source statement. Since the Heron values are sixteen times
;; squared areas, the positive area ratio is rational exactly when their
;; quotient has a rational square root.
(defun putnambench-putnam-2018-a6-statement
    (ab ac ad bc bd cd)
  (implies
   (and
    (rationalp ab)
    (rationalp ac)
    (rationalp ad)
    (rationalp bc)
    (rationalp bd)
    (rationalp cd)
    (< 0 ab)
    (< 0 ac)
    (< 0 ad)
    (< 0 bc)
    (< 0 bd)
    (< 0 cd)
    (< 0 (putnam-2018-a6-heron-sixteen ab ac bc))
    (< 0 (putnam-2018-a6-heron-sixteen ab ad bd))
    (< 0 (putnam-2018-a6-heron-sixteen ac ad cd))
    (< 0 (putnam-2018-a6-heron-sixteen bc bd cd))
    (equal
     (putnam-2018-a6-scaled-gram-determinant
      ab ac ad bc bd cd)
     0))
   (putnam-2018-a6-rational-square-p
    (/
     (putnam-2018-a6-heron-sixteen ab ac bc)
     (putnam-2018-a6-heron-sixteen ab ad bd)))))

(value-triple :itpeval-statement-checked)
:q
