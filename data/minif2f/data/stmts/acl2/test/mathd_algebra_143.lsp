;; Statement-only formalization of miniF2F artifact mathd_algebra_143:
;; composing the real functions f(x) = x + 1 and g(x) = x^2 + 3 at x = 2
;; gives 8. This file contains no proof.
;;
;; ACL2 is first-order, so the two function hypotheses are represented by
;; exactly the instances used in the conclusion: g(2) and f(g(2)). Every
;; source pair determines these local values. Conversely, any two values
;; satisfying the antecedent are 7 and 8 and are realized by the source
;; functions. Thus this scalar implication is bidirectionally equivalent to
;; the source statement and does not restrict the real domain.

(in-package "ACL2")

(defun mathd-algebra-143-statement (g-at-2 f-at-g-2)
  (implies
   (and (equal g-at-2
               (+ (expt 2 2) 3))
        (equal f-at-g-2
               (+ g-at-2 1)))
   (equal f-at-g-2 8)))

(value-triple :itpeval-statement-checked)
:q
