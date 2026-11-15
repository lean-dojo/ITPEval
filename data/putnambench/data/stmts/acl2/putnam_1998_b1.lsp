;; Statement-only formalization of PutnamBench corpus artifact putnam_1998_b1:
;; the minimum over positive real x of the given quotient involving x and
;; 1/x is 6. This file contains no proof.

(in-package "ACL2")

(defun putnam-1998-b1-value (x)
  (/ (- (- (expt (+ x (/ 1 x)) 6)
           (+ (expt x 6)
              (/ 1 (expt x 6))))
        2)
     (+ (expt (+ x (/ 1 x)) 3)
        (+ (expt x 3)
           (/ 1 (expt x 3))))))

(defun putnam-1998-b1-admissible-p (x)
  (and (rationalp x)
       (< 0 x)))

;; Standard ACL2 has exact rational arithmetic rather than a primitive real
;; sort. On x > 0 the denominator is strictly positive, so the source quotient
;; is continuous. Positive rationals are dense in the positive reals; hence
;; its lower bound is 6 on all positive reals exactly when it is 6 on all
;; positive rationals. The exact rational point x = 1 supplies the source's
;; internal attainment witness. Thus the two clauses below are
;; bidirectionally equivalent to the source assertion that the real minimum
;; is 6, without replacing the real domain by a rational minimum problem.
;; This argument applies to the fixed displayed quotient expanded above; an
;; arbitrary function that could behave differently at irrational points is
;; neither introduced nor quantified by this statement.
(defun putnambench-putnam-1998-b1-statement (x)
  (and
   (putnam-1998-b1-admissible-p 1)
   (equal (putnam-1998-b1-value 1) 6)
   (implies
    (putnam-1998-b1-admissible-p x)
    (<= 6 (putnam-1998-b1-value x)))))

(value-triple :itpeval-statement-checked)
:q
