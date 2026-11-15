;; Statement-only formalization of miniF2F artifact mathd_algebra_137: a
;; natural number that becomes 598 when increased by four percent must equal
;; 575. This file contains no proof.

(in-package "ACL2")

(defun mathd-algebra-137-statement (x)
  (implies
   (and (natp x)
        (equal (+ x (* (/ 4 100) x)) 598))
   (equal x 575)))

(value-triple :itpeval-statement-checked)
:q
