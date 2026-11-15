;; Statement-only formalization of miniF2F corpus artifact
;; induction_11div10tonmn1ton: for every natural number n, 11 divides the
;; integer 10^n - (-1)^n. This file contains no proof.

(in-package "ACL2")

(defun induction-11div10tonmn1ton-statement (n)
  (implies (natp n)
           (equal (mod (- (expt 10 n)
                          (expt -1 n))
                       11)
                  0)))

(value-triple :itpeval-statement-checked)
:q
