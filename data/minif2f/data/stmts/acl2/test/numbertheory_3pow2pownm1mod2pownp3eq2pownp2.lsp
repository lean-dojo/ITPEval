;; Statement-only formalization of miniF2F corpus artifact
;; numbertheory_3pow2pownm1mod2pownp3eq2pownp2: for every positive natural
;; number n, the remainder of 3^(2^n) - 1 modulo 2^(n+3) is 2^(n+2).
;; This file contains no proof.

(in-package "ACL2")

(defun numbertheory-3pow2pownm1mod2pownp3eq2pownp2-statement (n)
  (implies
   (and (natp n)
        (< 0 n))
   (equal
    (mod (- (expt 3 (expt 2 n))
            1)
         (expt 2 (+ n 3)))
    (expt 2 (+ n 2)))))

(value-triple :itpeval-statement-checked)
:q
