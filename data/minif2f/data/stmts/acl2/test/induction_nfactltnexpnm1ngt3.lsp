;; Statement-only formalization of miniF2F corpus artifact
;; induction_nfactltnexpnm1ngt3: for every natural number n at least 3,
;; n factorial is strictly less than n raised to n - 1. This file contains
;; no proof.

(in-package "ACL2")

(defun induction-nfactltnexpnm1ngt3-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (induction-nfactltnexpnm1ngt3-factorial (- n 1)))))

(defun induction-nfactltnexpnm1ngt3-statement (n)
  (implies (and (natp n)
                (<= 3 n))
           (< (induction-nfactltnexpnm1ngt3-factorial n)
              (expt n (- n 1)))))

(value-triple :itpeval-statement-checked)
:q
