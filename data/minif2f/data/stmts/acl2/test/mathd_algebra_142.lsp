;; Statement-only formalization of miniF2F artifact mathd_algebra_142: real
;; numbers satisfying 7m + b = -1 and -m + b = 7 have sum 5. The hypotheses
;; force m = -1 and b = 6, so ACL2's exact-rational encoding is equivalent to
;; the source statement over the reals. This file contains no proof.

(in-package "ACL2")

(defun mathd-algebra-142-statement (m b)
  (implies
   (and (rationalp m)
        (rationalp b)
        (equal (+ (* m 7) b) -1)
        (equal (+ (* m -1) b) 7))
   (equal (+ m b) 5)))

(value-triple :itpeval-statement-checked)
:q
