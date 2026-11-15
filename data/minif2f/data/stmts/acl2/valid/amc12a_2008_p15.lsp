;; Statement-only formalization of miniF2F artifact amc12a_2008_p15:
;; for the natural number k equal to 2008^2 + 2^2008, the remainder of
;; k^2 + 2^k modulo 10 is 6. This file contains no proof.

(in-package "ACL2")

(defun amc12a-2008-p15-statement (k)
  (implies
   (and (natp k)
        (equal k (+ (expt 2008 2)
                    (expt 2 2008))))
   (equal (mod (+ (expt k 2)
                  (expt 2 k))
               10)
          6)))

(value-triple :itpeval-statement-checked)
:q
