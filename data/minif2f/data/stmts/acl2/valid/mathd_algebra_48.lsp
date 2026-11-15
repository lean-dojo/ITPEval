;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_48:
;; the complex numbers q = 9 - 4i and e = -3 - 4i satisfy q - e = 12.
;; The hypotheses fix both variables to Gaussian integers, so ACL2's exact
;; number domain represents every satisfying source-complex tuple without
;; loss. This file contains no proof.

(in-package "ACL2")

(defun mathd-algebra-48-statement (q e)
  (implies
   (and (acl2-numberp q)
        (acl2-numberp e)
        (equal q #c(9 -4))
        (equal e #c(-3 -4)))
   (equal (- q e) 12)))

(value-triple :itpeval-statement-checked)
:q
