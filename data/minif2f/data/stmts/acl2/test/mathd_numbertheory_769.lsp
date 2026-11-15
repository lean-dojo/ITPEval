;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_769: the sum 129^34 + 96^38 has remainder 9 modulo 11.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-769-statement ()
  (equal (mod (+ (expt 129 34)
                 (expt 96 38))
              11)
         9))

(value-triple :itpeval-statement-checked)
:q
