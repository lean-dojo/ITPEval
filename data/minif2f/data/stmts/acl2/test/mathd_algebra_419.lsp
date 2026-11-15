;; Statement-only formalization of miniF2F artifact mathd_algebra_419: real
;; numbers a = -1 and b = 5 make -a - b^2 + 3*(a*b) equal -39. ACL2 uses
;; exact rationals; the hypotheses force these integer values, so the domain
;; representation is bidirectionally equivalent. This file contains no proof.

(in-package "ACL2")

(defun mathd-algebra-419-statement (a b)
  (implies
   (and (rationalp a)
        (rationalp b)
        (equal a -1)
        (equal b 5))
   (equal (+ (- (- a)
                (expt b 2))
             (* 3 (* a b)))
          -39)))

(value-triple :itpeval-statement-checked)
:q
