;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_110:
;; complex numbers q = 2 - 2i and e = 5 + 5i have product 20. This file
;; contains no proof.

(in-package "ACL2")

(defun mathd-algebra-110-statement (q e)
  (implies
   (and (acl2-numberp q)
        (acl2-numberp e)
        (equal q #c(2 -2))
        (equal e #c(5 5)))
   (equal (* q e) 20)))

(value-triple :itpeval-statement-checked)
:q
