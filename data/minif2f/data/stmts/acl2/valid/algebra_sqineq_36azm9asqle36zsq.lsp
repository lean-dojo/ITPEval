;; Statement-only formalization of miniF2F corpus artifact
;; algebra_sqineq_36azm9asqle36zsq: for all real numbers z and a,
;; 36*(a*z) - 9*a^2 is at most 36*z^2. This file contains no proof.
;;
;; The exact-rational statement below is bidirectionally equivalent to the
;; real statement. The real theorem immediately restricts to rational z and
;; a. Conversely, if the real inequality failed, its continuous polynomial
;; difference would remain negative on a neighborhood containing a rational
;; pair, contradicting the rational statement.

(in-package "ACL2")

(defun algebra-sqineq-36azm9asqle36zsq-statement (z a)
  (implies
   (and (rationalp z)
        (rationalp a))
   (<= (- (* 36 (* a z))
          (* 9 (expt a 2)))
       (* 36 (expt z 2)))))

(value-triple :itpeval-statement-checked)
:q
