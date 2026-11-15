;; Statement-only formalization of PutnamBench corpus artifact
;; putnam_1967_a6: the maximum number of sign 4-tuples of nonzero real
;; solutions to two homogeneous linear equations is eight. This file contains
;; no proof.

(in-package "ACL2")

;; ACL2's exact ordered arithmetic represents the eight coefficients by
;; rationals, so the statement explicitly requires RATIONALP for each one.
;; This is equivalent to the source maximum over real coefficients. One
;; direction is immediate because rational matrices are real matrices. For
;; the converse, if a real matrix with nonzero first minor realized more than
;; eight sign tuples, choose one nonzero solution for each of those finitely
;; many tuples. Their equation equalities and strict sign requirements persist
;; in a sufficiently small neighborhood inside the rank-two matrix locus.
;; Density of rational matrices and of rational points in a rational solution
;; subspace then gives the same sign tuples over the rationals. The reverse
;; direction is immediate because every rational instance is a real instance.
;;
;; Each sign pattern below is realized only through an explicit existential
;; solution vector. No feasibility algorithm or preselected attaining matrix
;; is built into the statement.

(defun putnam-1967-a6-det (u1 u2 v1 v2)
  (- (* u1 v2) (* u2 v1)))

(defun putnam-1967-a6-has-sign-p (value sign)
  (if (equal sign 1)
      (< 0 value)
    (< value 0)))

(defun-sk putnam-1967-a6-sign-realized-p
    (a1 a2 a3 a4 b1 b2 b3 b4 s1 s2 s3 s4)
  (exists (x1 x2 x3 x4)
    (and
     (rationalp x1)
     (rationalp x2)
     (rationalp x3)
     (rationalp x4)
     (putnam-1967-a6-has-sign-p x1 s1)
     (putnam-1967-a6-has-sign-p x2 s2)
     (putnam-1967-a6-has-sign-p x3 s3)
     (putnam-1967-a6-has-sign-p x4 s4)
     (equal
      (+ (* a1 x1) (* a2 x2) (* a3 x3) (* a4 x4))
      0)
     (equal
      (+ (* b1 x1) (* b2 x2) (* b3 x3) (* b4 x4))
      0))))

(defun putnam-1967-a6-sign-patterns ()
  '((-1 -1 -1 -1)
    (-1 -1 -1  1)
    (-1 -1  1 -1)
    (-1 -1  1  1)
    (-1  1 -1 -1)
    (-1  1 -1  1)
    (-1  1  1 -1)
    (-1  1  1  1)
    ( 1 -1 -1 -1)
    ( 1 -1 -1  1)
    ( 1 -1  1 -1)
    ( 1 -1  1  1)
    ( 1  1 -1 -1)
    ( 1  1 -1  1)
    ( 1  1  1 -1)
    ( 1  1  1  1)))

(defun putnam-1967-a6-count-patterns
    (patterns a1 a2 a3 a4 b1 b2 b3 b4)
  (if (endp patterns)
      0
    (+ (if (putnam-1967-a6-sign-realized-p
            a1 a2 a3 a4 b1 b2 b3 b4
            (nth 0 (car patterns))
            (nth 1 (car patterns))
            (nth 2 (car patterns))
            (nth 3 (car patterns)))
           1
         0)
       (putnam-1967-a6-count-patterns
        (cdr patterns) a1 a2 a3 a4 b1 b2 b3 b4))))

(defun putnam-1967-a6-numtuples
    (a1 a2 a3 a4 b1 b2 b3 b4)
  (putnam-1967-a6-count-patterns
   (putnam-1967-a6-sign-patterns)
   a1 a2 a3 a4 b1 b2 b3 b4))

(defun-sk putnam-1967-a6-attaining-matrix-exists-p ()
  (exists (a1 a2 a3 a4 b1 b2 b3 b4)
    (and
     (rationalp a1)
     (rationalp a2)
     (rationalp a3)
     (rationalp a4)
     (rationalp b1)
     (rationalp b2)
     (rationalp b3)
     (rationalp b4)
     (not (equal (putnam-1967-a6-det a1 a2 b1 b2) 0))
     (equal
      (putnam-1967-a6-numtuples
       a1 a2 a3 a4 b1 b2 b3 b4)
      8))))

(defun putnambench-putnam-1967-a6-statement
    (a1 a2 a3 a4 b1 b2 b3 b4)
  (and
   (putnam-1967-a6-attaining-matrix-exists-p)
   (implies
    (and
     (rationalp a1)
     (rationalp a2)
     (rationalp a3)
     (rationalp a4)
     (rationalp b1)
     (rationalp b2)
     (rationalp b3)
     (rationalp b4)
     (not (equal (putnam-1967-a6-det a1 a2 b1 b2) 0)))
    (<= (putnam-1967-a6-numtuples
         a1 a2 a3 a4 b1 b2 b3 b4)
        8))))

(value-triple :itpeval-statement-checked)
:q
