;; Statement-only formalization of miniF2F artifact mathd_algebra_141: real
;; numbers with product 180 and twice their sum equal to 54 have sum of
;; squares 369. ACL2 uses exact rationals; the hypotheses force the two
;; numbers to be 12 and 15, so this is equivalent. This file contains no proof.

(in-package "ACL2")

(defun mathd-algebra-141-statement (a b)
  (implies
   (and (rationalp a)
        (rationalp b)
        (equal (* a b) 180)
        (equal (* 2 (+ a b)) 54))
   (equal (+ (expt a 2)
             (expt b 2))
          369)))

(value-triple :itpeval-statement-checked)
:q
