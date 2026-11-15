;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_433:
;; evaluating at 8 a real function defined by
;; f(x) = 3*sqrt(2*x - 7) - 8 gives f(8) = 1. This file contains no proof.
;;
;; The Rocq, Isabelle, and Metamath sources state 1; the Lean source's 19
;; conflicts with its displayed formula, whose value at 8 is 1.
;;
;; The defining hypothesis uniquely determines the source function, and the
;; conclusion observes only its value at 8. Instantiating the definition there
;; gives the local relation below, with the principal square root represented
;; by its nonnegative-root characterization. Conversely, any values satisfying
;; this relation extend to the source function defined by the displayed
;; formula. The relation forces sqrt-nine = 3 and f-at-eight = 1, so every
;; satisfying real pair is rational; the guards therefore preserve all source
;; instances rather than restricting the real domain.

(in-package "ACL2")

(defun mathd-algebra-433-statement (f-at-eight sqrt-nine)
  (implies
   (and (rationalp f-at-eight)
        (rationalp sqrt-nine)
        (<= 0 sqrt-nine)
        (equal (* sqrt-nine sqrt-nine) 9)
        (equal f-at-eight
               (- (* 3 sqrt-nine) 8)))
   (equal f-at-eight 1)))

(value-triple :itpeval-statement-checked)
:q
