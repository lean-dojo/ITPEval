;; Statement-only formalization of miniF2F artifact mathd_numbertheory_345:
;; the sum of the natural numbers from 2000 through 2006 has remainder 0
;; modulo 7. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-345-statement ()
  (equal (mod (+ (+ (+ (+ (+ (+ 2000 2001)
                              2002)
                           2003)
                        2004)
                     2005)
                  2006)
              7)
         0))

(value-triple :itpeval-statement-checked)
:q
