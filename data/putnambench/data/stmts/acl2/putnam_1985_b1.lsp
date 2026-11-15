;; Statement-only formalization of PutnamBench corpus artifact putnam_1985_b1:
;; the five distinct integers -2,-1,0,1,2 minimize the number of nonzero
;; coefficients of a monic polynomial with five distinct integer roots.
;; This file contains no proof.

(in-package "ACL2")

(defun putnam-1985-b1-integer-list-p (values)
  (if (consp values)
      (and (integerp (car values))
           (putnam-1985-b1-integer-list-p (cdr values)))
    (equal values nil)))

(defun putnam-1985-b1-distinct-from-p (value values)
  (if (consp values)
      (and (not (equal value (car values)))
           (putnam-1985-b1-distinct-from-p value (cdr values)))
    t))

(defun putnam-1985-b1-pairwise-distinct-p (values)
  (if (consp values)
      (and (putnam-1985-b1-distinct-from-p
            (car values) (cdr values))
           (putnam-1985-b1-pairwise-distinct-p (cdr values)))
    t))

;; If COEFFICIENTS lists c_0,...,c_n in ascending degree order, this returns
;; the coefficient list of (x-M)*(c_0+c_1*x+...+c_n*x^n).
(defun putnam-1985-b1-multiply-linear
    (coefficients m previous)
  (if (consp coefficients)
      (cons (+ (* (- m) (car coefficients)) previous)
            (putnam-1985-b1-multiply-linear
             (cdr coefficients) m (car coefficients)))
    (list previous)))

(defun putnam-1985-b1-polynomial-from-roots (roots)
  (if (consp roots)
      (putnam-1985-b1-multiply-linear
       (putnam-1985-b1-polynomial-from-roots (cdr roots))
       (car roots)
       0)
    (list 1)))

(defun putnam-1985-b1-count-nonzero (coefficients)
  (if (consp coefficients)
      (+ (if (equal (car coefficients) 0) 0 1)
         (putnam-1985-b1-count-nonzero (cdr coefficients)))
    0))

(defun putnam-1985-b1-solution ()
  (list -2 -1 0 1 2))

;; A length-five integer list is canonically the source function Fin 5 -> Z.
;; Expanding the five linear factors gives integer coefficients, whose
;; embedding into the reals preserves exactly which coefficients are zero.
(defun putnambench-putnam-1985-b1-statement (roots)
  (let ((solution (putnam-1985-b1-solution)))
    (and
     (putnam-1985-b1-pairwise-distinct-p solution)
     (implies
      (and
       (true-listp roots)
       (equal (len roots) 5)
       (putnam-1985-b1-integer-list-p roots)
       (putnam-1985-b1-pairwise-distinct-p roots))
      (<=
       (putnam-1985-b1-count-nonzero
        (putnam-1985-b1-polynomial-from-roots solution))
       (putnam-1985-b1-count-nonzero
        (putnam-1985-b1-polynomial-from-roots roots)))))))

(value-triple :itpeval-statement-checked)
:q
