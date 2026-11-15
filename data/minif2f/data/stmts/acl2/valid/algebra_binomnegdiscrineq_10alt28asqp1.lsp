;; Statement-only formalization of miniF2F corpus artifact
;; algebra_binomnegdiscrineq_10alt28asqp1: for every real number a,
;; 10*a is at most 28*a^2 + 1. This file contains no proof.
;;
;; The exact-rational statement below is bidirectionally equivalent to the
;; real statement. The real theorem restricts immediately to rationals.
;; Conversely, a real counterexample would make the continuous polynomial
;; 28*a^2 + 1 - 10*a negative on a neighborhood containing a rational
;; counterexample.

(in-package "ACL2")

(defun algebra-binomnegdiscrineq-10alt28asqp1-statement (a)
  (implies
   (rationalp a)
   (<= (* 10 a)
       (+ (* 28 (expt a 2))
          1))))

(value-triple :itpeval-statement-checked)
:q
