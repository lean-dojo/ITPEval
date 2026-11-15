;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_314:
;; for a natural number n equal to 11, (1/4)^(n+1) times 2^(2*n) equals
;; 1/4. This file contains no proof.

(in-package "ACL2")

(defun mathd-algebra-314-statement (n)
  (implies
   (and (natp n)
        (equal n 11))
   (equal (* (expt (/ 1 4) (+ n 1))
             (expt 2 (* 2 n)))
          (/ 1 4))))

(value-triple :itpeval-statement-checked)
:q
