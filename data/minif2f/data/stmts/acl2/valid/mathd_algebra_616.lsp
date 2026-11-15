;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_616:
;; the real functions f(x) = x^3 + 2*x + 1 and g(x) = x - 1 satisfy
;; f(g(1)) = 1. This file contains no proof.
;;
;; ACL2 is first-order, so the two function hypotheses are represented by
;; exactly the observations used in the conclusion: g(1) and f(g(1)). The
;; antecedent is the source hypotheses instantiated at 1 and g(1). Every
;; source pair supplies these observations. Conversely, the antecedent forces
;; them to be 0 and 1, and they are realized by the source functions. Thus
;; this observation implication is bidirectionally equivalent to the source
;; statement. The equalities force exact integer values, so unrestricted ACL2
;; parameters do not narrow the source real domain.

(in-package "ACL2")

(defun mathd-algebra-616-statement (g-at-1 f-at-g-at-1)
  (implies
   (and
    (equal g-at-1
           (- 1 1))
    (equal f-at-g-at-1
           (+ (expt g-at-1 3)
              (* 2 g-at-1)
              1)))
   (equal f-at-g-at-1 1)))

(value-triple :itpeval-statement-checked)
:q
