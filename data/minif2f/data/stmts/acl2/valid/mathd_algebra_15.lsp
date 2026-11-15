;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_15:
;; a positive-natural binary function given by s(a,b) = a^b + b^a has
;; s(2,6) = 100. This file contains no proof.
;;
;; The source hypothesis fixes every positive-natural value of s. The
;; definition below constructs one such function, choosing 0 only where the
;; source hypothesis imposes no condition. Thus every source function agrees
;; with it at (2,6), and this function supplies the converse source instance,
;; so the closed predicate is bidirectionally equivalent to the source
;; implication.

(in-package "ACL2")

(defun mathd-algebra-15-s (a b)
  (if (and (natp a)
           (natp b)
           (< 0 a)
           (< 0 b))
      (+ (expt a b)
         (expt b a))
    0))

(defun mathd-algebra-15-statement ()
  (equal (mathd-algebra-15-s 2 6)
         100))

(value-triple :itpeval-statement-checked)
:q
