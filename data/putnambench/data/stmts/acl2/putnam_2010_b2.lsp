;; Statement-only formalization of PutnamBench corpus artifact putnam_2010_b2:
;; noncollinear plane points with integer coordinates and integer pairwise
;; distances have minimum possible distance AB equal to 3. This file contains
;; no proof.

(in-package "ACL2")

(defun putnam-2010-b2-squared-distance (x1 y1 x2 y2)
  (+ (* (- x2 x1) (- x2 x1))
     (* (- y2 y1) (- y2 y1))))

(defun putnam-2010-b2-determinant (ax ay bx by cx cy)
  (- (* (- bx ax) (- cy ay))
     (* (- by ay) (- cx ax))))

;; For a natural number x, this finite search holds exactly when x is the
;; square of a natural number. Thus it expresses internally that the
;; corresponding nonnegative Euclidean distance is an integer.
(defun putnam-2010-b2-square-witness-down-p (x candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (zp candidate)
      (equal x 0)
    (or (equal (* candidate candidate) x)
        (putnam-2010-b2-square-witness-down-p
         x
         (- candidate 1)))))

(defun putnam-2010-b2-perfect-square-p (x)
  (and (natp x)
       (putnam-2010-b2-square-witness-down-p x x)))

(defun putnam-2010-b2-configuration-p
    (ax ay bx by cx cy)
  (and (integerp ax)
       (integerp ay)
       (integerp bx)
       (integerp by)
       (integerp cx)
       (integerp cy)
       (putnam-2010-b2-perfect-square-p
        (putnam-2010-b2-squared-distance ax ay bx by))
       (putnam-2010-b2-perfect-square-p
        (putnam-2010-b2-squared-distance ax ay cx cy))
       (putnam-2010-b2-perfect-square-p
        (putnam-2010-b2-squared-distance bx by cx cy))
       (not (equal (putnam-2010-b2-determinant
                    ax ay bx by cx cy)
                   0))))

;; A=(0,0), B=(3,0), C=(0,4) attains the distance AB=3.
(defun putnam-2010-b2-attainment-certificate-p ()
  (and
   (putnam-2010-b2-configuration-p 0 0 3 0 0 4)
   (equal (putnam-2010-b2-squared-distance 0 0 3 0)
          9)))

(defun putnambench-putnam-2010-b2-statement
    (ax ay bx by cx cy)
  (and
   (putnam-2010-b2-attainment-certificate-p)
   (implies
    (putnam-2010-b2-configuration-p ax ay bx by cx cy)
    (<= 9
        (putnam-2010-b2-squared-distance ax ay bx by)))))

(value-triple :itpeval-statement-checked)
:q
