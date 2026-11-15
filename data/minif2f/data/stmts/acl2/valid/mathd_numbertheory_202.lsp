;; Statement-only formalization of miniF2F artifact mathd_numbertheory_202:
;; the natural-number remainder of 19^19 plus 99^99 modulo 10 is 8.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-202-statement ()
  (equal (mod (+ (expt 19 19)
                 (expt 99 99))
              10)
         8))

(value-triple :itpeval-statement-checked)
:q
