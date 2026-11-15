;; Statement-only formalization of miniF2F corpus artifact amc12a_2013_p4:
;; the real-number identity (2^2014 + 2^2012) / (2^2014 - 2^2012) = 5/3.
;; This file contains no proof.

(in-package "ACL2")

(defun amc12a-2013-p4-statement ()
  (equal (/ (+ (expt 2 2014)
               (expt 2 2012))
            (- (expt 2 2014)
               (expt 2 2012)))
         (/ 5 3)))

(value-triple :itpeval-statement-checked)
:q
