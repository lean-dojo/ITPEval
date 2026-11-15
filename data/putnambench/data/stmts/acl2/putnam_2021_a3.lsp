;; Statement-only formalization of PutnamBench corpus artifact putnam_2021_a3:
;; the positive integers N whose sphere x^2+y^2+z^2=N contains an
;; integer-coordinate regular tetrahedron are exactly N=3*m^2 for m>0.
;; This file contains no proof.

(in-package "ACL2")

;; ACL2 has no primitive existential term, so DEFUN-SK below provides the
;; community-standard first-order encoding of the source's unbounded
;; existential quantifiers. A point is represented by a length-three list of
;; integer coordinates.

(defun putnam-2021-a3-sphere-point-p (p n)
  (and
   (true-listp p)
   (equal (len p) 3)
   (integerp (car p))
   (integerp (cadr p))
   (integerp (caddr p))
   (equal
    (+ (* (car p) (car p))
       (* (cadr p) (cadr p))
       (* (caddr p) (caddr p)))
    n)))

(defun putnam-2021-a3-squared-distance (p q)
  (+ (* (- (car p) (car q))
        (- (car p) (car q)))
     (* (- (cadr p) (cadr q))
        (- (cadr p) (cadr q)))
     (* (- (caddr p) (caddr q))
        (- (caddr p) (caddr q)))))

;; For integer-coordinate points, six Euclidean distances are one common
;; positive real number exactly when their six squared distances are one
;; common positive integer.
(defun putnam-2021-a3-regular-tetrahedron-p (a b c d)
  (let ((side-square
         (putnam-2021-a3-squared-distance a b)))
    (and
     (< 0 side-square)
     (equal (putnam-2021-a3-squared-distance a c)
            side-square)
     (equal (putnam-2021-a3-squared-distance a d)
            side-square)
     (equal (putnam-2021-a3-squared-distance b c)
            side-square)
     (equal (putnam-2021-a3-squared-distance b d)
            side-square)
     (equal (putnam-2021-a3-squared-distance c d)
            side-square))))

(defun-sk putnam-2021-a3-tetrahedron-exists-p (n)
  (exists
   (a b c d)
   (and
    (putnam-2021-a3-sphere-point-p a n)
    (putnam-2021-a3-sphere-point-p b n)
    (putnam-2021-a3-sphere-point-p c n)
    (putnam-2021-a3-sphere-point-p d n)
    (putnam-2021-a3-regular-tetrahedron-p a b c d))))

(defun-sk putnam-2021-a3-solution-member-p (n)
  (exists
   (m)
   (and
    (integerp m)
    (< 0 m)
    (equal n (* 3 m m)))))

;; The root predicate is universally closed over N by the ACL2
;; statement-corpus convention. Nsphere and intcoords from the source are
;; definitionally eliminated by the exact integer-coordinate sphere predicate.
(defun putnambench-putnam-2021-a3-statement (n)
  (implies
   (natp n)
   (equal
    (and
     (< 0 n)
     (putnam-2021-a3-tetrahedron-exists-p n))
    (putnam-2021-a3-solution-member-p n))))

(value-triple :itpeval-statement-checked)
:q
