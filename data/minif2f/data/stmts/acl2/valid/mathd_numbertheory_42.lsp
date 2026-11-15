;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_42: the least two positive natural-number solutions of
;; 27*n congruent to 17 modulo 40 have sum 62. This file contains no proof.

(in-package "ACL2")

;; The interval bounds select the least positive solution and the next one,
;; matching the equivalent set-minimum formulation in the source corpus.
(defun mathd-numbertheory-42-statement (u v)
  (implies
   (and (natp u)
        (natp v)
        (equal (mod (* 27 u) 40) 17)
        (equal (mod (* 27 v) 40) 17)
        (< u 40)
        (< v 80)
        (< 40 v))
   (equal (+ u v) 62)))

(value-triple :itpeval-statement-checked)
:q
