;; Statement-only formalization of PutnamBench corpus artifact putnam_1985_a6:
;; the coefficient-square sums of every positive power of 3*x^2+7*x+2 and
;; 6*x^2+5*x+1 are equal, with the latter polynomial taking value 1 at zero.
;; This file contains no proof.

(in-package "ACL2")

;; Coefficients are stored in ascending degree order. Both source polynomials
;; have integer coefficients, and addition, multiplication, powering, and the
;; coefficient-square sum preserve integrality. Thus these exact coefficient
;; lists compute the same polynomials and Gamma values as the source real
;; polynomial operations under the canonical embedding of integers into the
;; reals; no arbitrary real coefficient domain is restricted.

(defun putnam-1985-a6-poly-add (left right)
  (cond
   ((consp left)
    (if (consp right)
        (cons (+ (car left) (car right))
              (putnam-1985-a6-poly-add
               (cdr left) (cdr right)))
      left))
   (t right)))

(defun putnam-1985-a6-poly-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (putnam-1985-a6-poly-scale
             scalar (cdr polynomial)))
    nil))

(defun putnam-1985-a6-poly-multiply (left right)
  (if (consp left)
      (putnam-1985-a6-poly-add
       (putnam-1985-a6-poly-scale (car left) right)
       (cons 0
             (putnam-1985-a6-poly-multiply
              (cdr left) right)))
    nil))

(defun putnam-1985-a6-poly-power (polynomial exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (list 1)
    (putnam-1985-a6-poly-multiply
     polynomial
     (putnam-1985-a6-poly-power
      polynomial (- exponent 1)))))

(defun putnam-1985-a6-gamma (polynomial)
  (if (consp polynomial)
      (+ (* (car polynomial) (car polynomial))
         (putnam-1985-a6-gamma (cdr polynomial)))
    0))

(defun putnambench-putnam-1985-a6-statement (n)
  (implies
   (and (natp n)
        (<= 1 n))
   (let ((f '(2 7 3))
         (g '(1 5 6)))
     (and
      (equal (car g) 1)
      (equal
       (putnam-1985-a6-gamma
        (putnam-1985-a6-poly-power f n))
       (putnam-1985-a6-gamma
        (putnam-1985-a6-poly-power g n)))))))

(value-triple :itpeval-statement-checked)
:q
