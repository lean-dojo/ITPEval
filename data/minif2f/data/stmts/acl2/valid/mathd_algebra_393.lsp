;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_393:
;; the inverse of the real bijection x |-> 4*x^3 + 1 sends 33 to 2. This file
;; contains no proof.
;;
;; Let y = sigma^{-1}(33) and s = sigma(y). The defining formula gives
;; s = 4*y^3 + 1, while the right inverse law gives s = 33. These are exactly
;; the two observations below. Their real equations force y = 2 and s = 33,
;; so every satisfying real observation is rational. Conversely, the guarded
;; ACL2 observation embeds unchanged into the reals and is realized by the
;; source bijection. Thus the rational guards omit no source instance.

(in-package "ACL2")

(defun mathd-algebra-393-statement
    (inverse-at-thirty-three sigma-at-inverse-at-thirty-three)
  (implies
   (and
    (rationalp inverse-at-thirty-three)
    (rationalp sigma-at-inverse-at-thirty-three)
    (equal sigma-at-inverse-at-thirty-three
           (+ (* 4 (expt inverse-at-thirty-three 3)) 1))
    (equal sigma-at-inverse-at-thirty-three 33))
   (equal inverse-at-thirty-three 2)))

(value-triple :itpeval-statement-checked)
:q
