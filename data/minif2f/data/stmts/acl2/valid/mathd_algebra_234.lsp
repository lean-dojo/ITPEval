;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_234:
;; a real number d satisfying (27/125)*d = 9/25 also satisfies
;; (3/5)*d^3 = 25/9. This file contains no proof.
;;
;; The hypothesis forces d = 5/3, so every satisfying real assignment is
;; rational. Conversely, every guarded ACL2 assignment embeds unchanged into
;; the reals. Thus exact rational arithmetic preserves and reflects the source
;; implication.

(in-package "ACL2")

(defun mathd-algebra-234-statement (d)
  (implies
   (and (rationalp d)
        (equal (* (/ 27 125) d)
               (/ 9 25)))
   (equal (* (/ 3 5) (expt d 3))
          (/ 25 9))))

(value-triple :itpeval-statement-checked)
:q
