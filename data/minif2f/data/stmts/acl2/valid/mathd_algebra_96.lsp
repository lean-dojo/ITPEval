;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_96:
;; three natural-logarithm differences around a cycle determine the real
;; parameter a as -8. This file contains no proof.
;;
;; Write p = ln(x)-ln(y), q = ln(y)-ln(z), and r = ln(z)-ln(x). These
;; coordinates always satisfy p+q+r = 0, and the source hypotheses become
;; p = a, q = 15, and r = -7. They force p and a to be -8, so every
;; satisfying real coordinate tuple is rational. Conversely, any encoded
;; tuple satisfying the cycle equation reconstructs positive source values:
;; take ln(z)=0, ln(y)=q, ln(x)=p+q, then exponentiate. Thus the rational
;; guards preserve the complete satisfying locus rather than restricting it.
;;
;; Lean, Rocq, and Isabelle quantify a over all reals. The extra condition
;; a > 0 in the HOL Light and Metamath renderings is incompatible with the
;; displayed equations, so it is omitted as a conversion artifact rather
;; than used to make the implication vacuous.

(in-package "ACL2")

(defun mathd-algebra-96-statement
    (log-x-minus-log-y log-y-minus-log-z log-z-minus-log-x a)
  (implies
   (and (rationalp log-x-minus-log-y)
        (rationalp log-y-minus-log-z)
        (rationalp log-z-minus-log-x)
        (rationalp a)
        (equal (+ log-x-minus-log-y
                  log-y-minus-log-z
                  log-z-minus-log-x)
               0)
        (equal log-x-minus-log-y a)
        (equal log-y-minus-log-z 15)
        (equal log-z-minus-log-x -7))
   (equal a -8)))

(value-triple :itpeval-statement-checked)
:q
