;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_233: the integer representative of the inverse of 24
;; modulo 11^2 is 116. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-233-statement (b)
  (implies
   (and (integerp b)
        (<= 0 b)
        (< b (* 11 11))
        (equal (mod (* b 24) (* 11 11)) 1))
   (equal b 116)))

(value-triple :itpeval-statement-checked)
:q
