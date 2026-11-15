;; Statement-only formalization of miniF2F artifact mathd_algebra_160: real
;; numbers n and x satisfying n + x = 97 and n + 5*x = 265 also satisfy
;; n + 2*x = 139. The hypotheses force x = 42 and n = 55, so any real
;; counterexample would be rational; conversely, ACL2 rationals embed in the
;; reals. Thus this exact-rational encoding is bidirectionally equivalent to
;; the source statement over the reals. This file contains no proof.

(in-package "ACL2")

(defun mathd-algebra-160-statement (n x)
  (implies
   (and (rationalp n)
        (rationalp x)
        (equal (+ n x) 97)
        (equal (+ n (* 5 x)) 265))
   (equal (+ n (* 2 x)) 139)))

(value-triple :itpeval-statement-checked)
:q
