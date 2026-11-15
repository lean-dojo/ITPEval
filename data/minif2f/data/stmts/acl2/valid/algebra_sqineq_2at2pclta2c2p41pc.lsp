;; Statement-only formalization of miniF2F corpus artifact
;; algebra_sqineq_2at2pclta2c2p41pc: for all real numbers a and c,
;; 2*a*(2+c) is at most a^2+c^2+4*(1+c). This file contains no proof.
;;
;; The exact-rational statement below is bidirectionally equivalent to the
;; real statement. The real theorem immediately restricts to rational a and
;; c. Conversely, if the real inequality failed, its continuous polynomial
;; difference would remain negative on a neighborhood containing a rational
;; pair, contradicting the rational statement.

(in-package "ACL2")

(defun algebra-sqineq-2at2pclta2c2p41pc-statement (a c)
  (implies
   (and (rationalp a)
        (rationalp c))
   (<= (* 2 a (+ 2 c))
       (+ (+ (expt a 2)
             (expt c 2))
          (* 4 (+ 1 c))))))

(value-triple :itpeval-statement-checked)
:q
