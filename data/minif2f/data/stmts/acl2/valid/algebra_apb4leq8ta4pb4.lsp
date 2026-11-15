;; Statement-only formalization of miniF2F corpus artifact
;; algebra_apb4leq8ta4pb4: for positive real numbers a and b, the fourth
;; power of their sum is at most eight times the sum of their fourth powers.
;; This file contains no proof.
;;
;; The exact-rational statement below is bidirectionally equivalent to the
;; real statement. The real theorem immediately restricts to positive
;; rationals. Conversely, if the real inequality failed, the continuous
;; polynomial difference 8*(a^4+b^4)-(a+b)^4 would remain negative on a
;; neighborhood containing a positive rational pair, contradicting the
;; rational statement.

(in-package "ACL2")

(defun algebra-apb4leq8ta4pb4-statement (a b)
  (implies
   (and (rationalp a)
        (rationalp b)
        (< 0 a)
        (< 0 b))
   (<= (expt (+ a b) 4)
       (* 8
          (+ (expt a 4)
             (expt b 4))))))

(value-triple :itpeval-statement-checked)
:q
