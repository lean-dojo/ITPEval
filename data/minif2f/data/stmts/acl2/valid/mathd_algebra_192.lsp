;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_192:
;; the complex numbers q = 11 - 5i, e = 11 + 5i, and d = 2i satisfy
;; q * e * d = 292i. The hypotheses fix every variable to a Gaussian integer,
;; so ACL2's exact number domain represents every satisfying source-complex
;; tuple without loss. This file contains no proof.

(in-package "ACL2")

(defun mathd-algebra-192-statement (q e d)
  (implies
   (and (acl2-numberp q)
        (acl2-numberp e)
        (acl2-numberp d)
        (equal q #c(11 -5))
        (equal e #c(11 5))
        (equal d #c(0 2)))
   (equal (* (* q e) d)
          #c(0 292))))

(value-triple :itpeval-statement-checked)
:q
