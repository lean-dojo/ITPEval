;; Statement-only formalization of miniF2F corpus artifact
;; mathd_algebra_398: positive real numbers satisfying two proportionality
;; equations satisfy 63 * a = 80 * c. This file contains no proof.
;;
;; ACL2 exact rational arithmetic is bidirectionally equivalent here. Since
;; c is positive, any real counterexample can be divided by c. The hypotheses
;; then force the normalized triple to be (80/63, 20/9, 1), which is rational,
;; and normalization preserves positivity, both equations, and failure of the
;; homogeneous conclusion. Conversely, every rational counterexample embeds
;; into the reals unchanged.

(in-package "ACL2")

(defun mathd-algebra-398-statement (a b c)
  (implies
   (and (rationalp a)
        (rationalp b)
        (rationalp c)
        (< 0 a)
        (< 0 b)
        (< 0 c)
        (equal (* 9 b) (* 20 c))
        (equal (* 7 a) (* 4 b)))
   (equal (* 63 a) (* 80 c))))

(value-triple :itpeval-statement-checked)
:q
