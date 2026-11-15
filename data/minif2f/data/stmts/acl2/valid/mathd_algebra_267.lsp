;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_267:
;; a real number x, distinct from 1 and -2, satisfying
;; (x + 1)/(x - 1) = (x - 2)/(x + 2), must equal 0. This file contains
;; no proof.
;;
;; The exclusions make both source denominators nonzero. Cross-multiplication
;; then reduces the equation over the reals to 6*x = 0, so every satisfying
;; real assignment has x = 0 and lies in the rational subfield represented
;; exactly by ACL2. Conversely, each guarded ACL2 assignment embeds unchanged
;; into the reals. Thus the rational guard loses no satisfying real assignment
;; and this predicate is bidirectionally equivalent to the source proposition.

(in-package "ACL2")

(defun mathd-algebra-267-statement (x)
  (implies
   (and (rationalp x)
        (not (equal x 1))
        (not (equal x -2))
        (equal (/ (+ x 1) (- x 1))
               (/ (- x 2) (+ x 2))))
   (equal x 0)))

(value-triple :itpeval-statement-checked)
:q
