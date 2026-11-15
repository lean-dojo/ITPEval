;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_323:
;; the inverse of the real bijection x |-> x^3 - 8 sends 19 to 3, so the
;; stated nested inverse evaluation is 3. This file contains no proof.
;;
;; Let y = sigma^{-1}(19). The right inverse law and the defining formula for
;; sigma give sigma(y) = 19 = y^3 - 8, while the left inverse law reduces
;; sigma^{-1}(sigma(y)) to y. These are exactly the three observations below.
;; Their real equations force y and the nested value to be 3 and sigma(y) to
;; be 19. Hence every satisfying real observation is rational, and conversely
;; each guarded ACL2 observation embeds unchanged into the reals; the rational
;; guards therefore omit no source instance.

(in-package "ACL2")

(defun mathd-algebra-323-statement
    (inverse-at-nineteen
     sigma-at-inverse-at-nineteen
     inverse-at-sigma-at-inverse-at-nineteen)
  (implies
   (and
    (rationalp inverse-at-nineteen)
    (rationalp sigma-at-inverse-at-nineteen)
    (rationalp inverse-at-sigma-at-inverse-at-nineteen)
    (equal sigma-at-inverse-at-nineteen
           (- (expt inverse-at-nineteen 3) 8))
    (equal sigma-at-inverse-at-nineteen 19)
    (equal inverse-at-sigma-at-inverse-at-nineteen
           inverse-at-nineteen))
   (equal inverse-at-sigma-at-inverse-at-nineteen 3)))

(value-triple :itpeval-statement-checked)
:q
