;; Statement-only formalization of miniF2F corpus artifact
;; algebra_sqineq_4bap1lt4bsqpap1sq: for all real numbers a and b,
;; 4*b*(a+1) is at most 4*b^2+(a+1)^2. This file contains no proof.
;;
;; The exact-rational statement below is bidirectionally equivalent to the
;; real statement. The real theorem immediately restricts to rational a and
;; b. Conversely, if the real inequality failed, its continuous polynomial
;; difference would remain negative on a neighborhood containing a rational
;; pair, contradicting the rational statement.

(in-package "ACL2")

(defun algebra-sqineq-4bap1lt4bsqpap1sq-statement (a b)
  (implies
   (and (rationalp a)
        (rationalp b))
   (<= (* 4 b (+ a 1))
       (+ (* 4 (expt b 2))
          (expt (+ a 1) 2)))))

(value-triple :itpeval-statement-checked)
:q
